use core::cell::UnsafeCell;
use core::hash::Hash;
use core::mem::ManuallyDrop;
use core::num::NonZeroUsize;
use core::ptr::NonNull;

use either::Either;

use crate::BRANCH_FACTOR;
use crate::BitArray;
use crate::RentPtr;
use crate::borrow::Consign;
use crate::borrow::Lend;

// LSB = Least Significant Bits
// MSB = Most Significant Bits
//
// TODO port to 32 bit architecture
// alignment of ptrs is 4 not 8 so bucket length is smaller

#[repr(align(2))]
pub struct Entry<K: Hash + Eq + Clone, V: Lend + Consign> {
    key: K,
    value: V,
}

// We ignore the 2 MSB of the hash, thus we can only hold 1073741824 (2^30) hashes
type H = u32;
const CHOP_OFF_TOP_TWO_BITS: u32 = !0xc0000000;
const PH_HASH_BITS_LEN: u32 = 25;
// 25 LSB are 25 LSB of the hash (we implicitly know at least 5 MSB of hash if we find this value)
// 7 MSB are 7 MSB of corresponding bucket length
#[repr(transparent)]
#[derive(Clone, Copy)]
struct PartialHash(u32);
impl PartialHash {
    fn full_hash(self, msb: u8) -> H {
        ((msb as u32) << PH_HASH_BITS_LEN) & (self.0 & (2u32.pow(PH_HASH_BITS_LEN) - 1))
    }
}

const CB_TAG_BITS_LEN: u32 = 3;
const CB_TAG_MASK: u32 = 2u32.pow(CB_TAG_BITS_LEN) - 1;
// tagged slice pointer, 3 LSB are the 3 LSB of the length of the slice
#[repr(transparent)]
#[derive(Copy)]
struct CollisionBucket<K: Hash + Eq + Clone, V: Lend + Consign>(NonNull<RentPtr<Entry<K, V>>>);
impl<K: Hash + Eq + Clone, V: Lend + Consign> Clone for CollisionBucket<K, V> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}

impl<K: Hash + Eq + Clone, V: Lend + Consign> CollisionBucket<K, V> {
    fn ptr_len(&self, phash: PartialHash) -> (NonNull<RentPtr<Entry<K, V>>>, usize) {
        // we will treat len as if it were a 10 bit integer
        let len = ((phash.0 >> (PH_HASH_BITS_LEN - CB_TAG_BITS_LEN)) & !CB_TAG_MASK) // 7 msb,
            & (self.0.as_ptr().addr() as u32 & CB_TAG_MASK); // 3 lsb
        let ptr = self.0.map_addr(|x| unsafe {
            NonZeroUsize::new_unchecked(x.get() & !(CB_TAG_MASK as usize))
        });
        (ptr, len as usize)
    }
    // SAFETY phash must corresponding hash found in HashBucketPair
    unsafe fn as_slice(&self, phash: PartialHash) -> &[RentPtr<Entry<K, V>>] {
        let (ptr, len) = self.ptr_len(phash);
        unsafe { core::slice::from_raw_parts(ptr.as_ptr(), len) }
    }
    // SAFETY phash must corresponding hash found in HashBucketPair
    unsafe fn as_slice_mut(&mut self, phash: PartialHash) -> &mut [RentPtr<Entry<K, V>>] {
        let (ptr, len) = self.ptr_len(phash);
        unsafe { core::slice::from_raw_parts_mut(ptr.as_ptr(), len) }
    }
}

// takes only 3 words, or 24 bytes
// modification of the kv pair present in champ for 64 bit architectures
// allows our node/value storage to be only 1.5 * BRANCH_FACTOR words
#[derive(Clone)]
#[repr(C)]
struct HashBucketPair<K: Hash + Eq + Clone, V: Lend + Consign> {
    phashes: [PartialHash; 2],
    buckets: [Option<CollisionBucket<K, V>>; 2],
}
impl<K: Hash + Eq + Clone, V: Lend + Consign> HashBucketPair<K, V> {
    fn bucket_as_slice(&self, idx: u8) -> Option<&[RentPtr<Entry<K, V>>]> {
        let idx: usize = if idx == 0 { 0 } else { 1 };
        let bucket = self.buckets[idx].as_ref()?;
        let phash = self.phashes[idx];
        Some(unsafe { bucket.as_slice(phash) })
    }
    fn bucket_as_slice_mut(&mut self, idx: u8) -> Option<&mut [RentPtr<Entry<K, V>>]> {
        let idx: usize = if idx == 0 { 0 } else { 1 };
        let bucket = self.buckets[idx].as_mut()?;
        let phash = self.phashes[idx];
        Some(unsafe { bucket.as_slice_mut(phash) })
    }
}

const fn scaled(b: usize) -> usize {
    3 * (b / 2)
}

// values stored front to back, like usual
// nodes stored back to front
union NodeValueStore<K: Hash + Eq + Clone, V: Lend + Consign> {
    bucket_pairs: ManuallyDrop<[HashBucketPair<K, V>; BRANCH_FACTOR / 2]>,
    nodes: [Option<NonNull<ChampNode<K, V>>>; scaled(BRANCH_FACTOR)],
}

struct ChampNode<K: Hash + Eq + Clone, V: Lend + Consign> {
    owned_indices: UnsafeCell<BitArray>,
    value_indices: BitArray,
    node_indices: BitArray,
    store: NodeValueStore<K, V>,
}
type PHashBucketSlice<'a, K, V> = (PartialHash, &'a [RentPtr<Entry<K, V>>]);
type PHashBucketMutSlice<'a, K, V> = (PartialHash, &'a mut [RentPtr<Entry<K, V>>]);
impl<K: Hash + Eq + Clone, V: Lend + Consign> ChampNode<K, V> {
    const fn empty() -> Self {
        unsafe { core::mem::zeroed() }
    }
    fn store_len(&self) -> u32 {
        self.value_indices.count_bits() + self.node_indices.count_bits()
    }
    fn get(&self, idx: u8) -> Option<Either<PHashBucketSlice<'_, K, V>, &Self>> {
        if let Some(value) = self.get_value(idx) {
            Some(Either::Left(value))
        } else if let Some(node) = self.get_node(idx) {
            Some(Either::Right(node))
        } else {
            None
        }
    }
    fn get_mut(&mut self, idx: u8) -> Option<Either<PHashBucketMutSlice<'_, K, V>, &mut Self>> {
        if self.owned_indices.get_mut().get(idx as usize) {
            if self.value_indices.get(idx as usize) {
                self.get_value_mut(idx).map(Either::Left)
            } else if self.node_indices.get(idx as usize) {
                self.get_node_mut(idx).map(Either::Right)
            } else {
                panic!(
                    "{idx} of {:x} owned but neither node or value bit set",
                    (self as *const Self).addr()
                );
            }
        } else {
            None
        }
    }
    fn bit_idx_to_node_idx(&self, bit_idx: u8) -> u8 {
        scaled(BRANCH_FACTOR) as u8 - 1 - self.node_indices.count_bits_up_to(bit_idx as usize) as u8
    }
    fn bit_idx_to_bucket_idx(&self, bit_idx: u8) -> (u8, u8) {
        let idx = self.value_indices.count_bits_up_to(bit_idx as usize) as u8;
        (idx % 2, idx / 2)
    }
    fn get_value(&self, idx: u8) -> Option<PHashBucketSlice<'_, K, V>> {
        if self.value_indices.get(idx as usize) {
            if idx as usize >= BRANCH_FACTOR / 2 {
                return None;
            }
            let (part, idx) = self.bit_idx_to_bucket_idx(idx);
            let bucket = unsafe { &self.store.bucket_pairs[idx as usize] };
            Some((
                bucket.phashes[part as usize],
                bucket
                    .bucket_as_slice(part)
                    .expect("Value idx is set, value must exist"),
            ))
        } else {
            None
        }
    }
    fn get_node(&self, idx: u8) -> Option<&Self> {
        if self.node_indices.get(idx as usize) {
            let idx = self.bit_idx_to_node_idx(idx);
            let node = unsafe { &self.store.nodes[idx as usize] };
            Some(unsafe {
                node.as_ref()
                    .expect("Node idx is set, node must exist")
                    .as_ref()
            })
        } else {
            None
        }
    }
    fn get_value_mut(&mut self, idx: u8) -> Option<PHashBucketMutSlice<'_, K, V>> {
        if self.owned_indices.get_mut().get(idx as usize) && self.value_indices.get(idx as usize) {
            if idx as usize >= BRANCH_FACTOR / 2 {
                return None;
            }
            let (part, idx) = self.bit_idx_to_bucket_idx(idx);
            let bucket = unsafe { &mut (*self.store.bucket_pairs)[idx as usize] };
            Some((
                bucket.phashes[part as usize],
                bucket
                    .bucket_as_slice_mut(part)
                    .expect("Value idx is set, value must exist"),
            ))
        } else {
            None
        }
    }
    fn get_node_mut(&mut self, idx: u8) -> Option<&mut Self> {
        if self.owned_indices.get_mut().get(idx as usize) && self.node_indices.get(idx as usize) {
            let idx = self.bit_idx_to_node_idx(idx);
            let node = unsafe { &mut self.store.nodes[idx as usize] };
            Some(unsafe {
                node.as_mut()
                    .expect("Node idx is set, node must exist")
                    .as_mut()
            })
        } else {
            None
        }
    }
    // hash_shift starts at 5 and will decrease with each recursion
    fn append_entry(&mut self, hash_shift: H, hash: H, entry: Entry<K, V>) {
        assert!(hash_shift < 6);
        let bit_idx = (hash >> (hash_shift * BRANCH_FACTOR.ilog2())) & (BRANCH_FACTOR as u32 - 1);
    }
}
