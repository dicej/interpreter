use {
    maplit::{btreemap, hashset},
    std::{
        cmp::Ordering,
        collections::{BTreeMap, HashSet},
    },
};

pub struct Allocator {
    capacity: usize,
    by_offset: BTreeMap<usize, usize>,
    by_size: BTreeMap<usize, HashSet<usize>>,
}

impl Allocator {
    pub fn new(capacity: usize) -> Self {
        Self {
            capacity,
            by_offset: btreemap![0 => capacity],
            by_size: btreemap![capacity => hashset![0]],
        }
    }

    fn remove(&mut self, offset: usize, size: usize) {
        let empty = {
            let offsets = self.by_size.get_mut(&size).unwrap();

            offsets.remove(&offset);

            offsets.is_empty()
        };

        if empty {
            self.by_size.remove(&size);
        }

        self.by_offset.remove(&offset);
    }

    pub fn allocate(&mut self, size: usize) -> Option<usize> {
        if size == 0 {
            return Some(self.capacity);
        }

        let (free_size, offset, empty) =
            if let Some((free_size, offsets)) = self.by_size.range_mut(size..).next() {
                let offset = offsets.iter().next().copied().unwrap();

                offsets.remove(&offset);

                (free_size, offset, offsets.is_empty())
            } else {
                return None;
            };

        if empty {
            self.by_size.remove(free_size);
        }

        self.by_offset.remove(&offset);

        if size < *free_size {
            let new_free_size = *free_size - size;
            let new_offset = offset + size;

            self.by_offset.insert(new_offset, new_free_size);
            self.by_size
                .entry(new_free_size)
                .or_default()
                .insert(new_offset);
        }

        Some(offset)
    }

    pub fn free(&mut self, mut offset: usize, mut size: usize) {
        if size == 0 {
            return;
        }

        if offset + size > self.capacity {
            panic!("invalid free: region exceeds capacity");
        }

        if self
            .by_offset
            .range(offset..(offset + size))
            .next()
            .is_some()
        {
            panic!("invalid free: region overlaps already-free region");
        }

        let merge_previous = self.by_offset.range(..offset).rev().next().filter(
            |(previous_offset, previous_size)| match offset
                .cmp(&(**previous_offset + **previous_size))
            {
                Ordering::Less => {
                    panic!("invalid free: region overlaps already-free region");
                }
                Ordering::Equal => true,
                Ordering::Greater => false,
            },
        );

        if let Some((previous_offset, previous_size)) = merge_previous {
            offset = *previous_offset;
            size += *previous_size;

            self.remove(*previous_offset, *previous_size);
        }

        let next_offset = offset + size;

        if let Some(next_size) = self.by_offset.get(&next_offset) {
            size += *next_size;

            self.remove(next_offset, *next_size);
        }

        self.by_offset.insert(offset, size);
        self.by_size.entry(size).or_default().insert(offset);
    }
}

#[cfg(test)]
mod test {
    use {
        super::*,
        proptest::{collection, prelude::Just, proptest, strategy::Strategy},
    };

    const MIN_CAPACITY: usize = 32;
    const MAX_CAPACITY: usize = 1024;
    const MAX_ITERATIONS_PER_CASE: usize = 100;
    const MAX_ALLOCATIONS_PER_ITERATION: usize = 100;

    #[derive(Debug)]
    struct Iteration {
        allocations: Vec<usize>,
        frees: Vec<usize>,
    }

    #[derive(Debug)]
    struct Case {
        capacity: usize,
        iterations: Vec<Iteration>,
    }

    impl Case {
        fn run(&self) {
            let allocator = Allocator::new(self.capacity);

            for iteration in &self.iterations {
                let regions = iteration
                    .allocations
                    .iter()
                    .map(|&size| (allocator.allocate(size), size))
                    .collect::<Vec<_>>();

                for &index in &iteration.frees {
                    if let (Some(offset), size) = regions[index] {
                        allocator.free(offset, size)
                    }
                }
            }
        }
    }

    fn arb_iteration(capacity: usize) -> impl Strategy<Value = Iteration> {
        collection::vec(0..capacity, 1..=MAX_ALLOCATIONS_PER_ITERATION).prop_flat_map(
            |allocations| {
                Just((0..allocations.len()).into_iter().collect::<Vec<_>>())
                    .prop_shuffle()
                    .prop_map(move |frees| Iteration {
                        allocations: allocations.clone(),
                        frees,
                    })
            },
        )
    }

    fn arb_case() -> impl Strategy<Value = Case> {
        (MIN_CAPACITY..=MAX_CAPACITY).prop_flat_map(|capacity| {
            collection::vec(arb_iteration(capacity), 1..=MAX_ITERATIONS_PER_CASE).prop_map(
                move |iterations| Case {
                    capacity,
                    iterations,
                },
            )
        })
    }

    proptest! {
        #[test]
        fn arbitrary_case(case in arb_case()) {
            case.run();
        }
    }
}
