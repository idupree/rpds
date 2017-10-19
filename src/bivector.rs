/* This file is part of rpds.
 *
 * rpds is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * rpds is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with rpds.  If not, see <http://www.gnu.org/licenses/>.
 */

use vector::Vector;

/// WIP
#[derive(Debug)]
pub struct BiVector<T> {
    left: Vector<T>,
    right: Vector<T>,
}

/// WIP rustdoc.  better name?
enum IndexMapping {
    Left(usize),
    Right(usize),
}

impl<T> BiVector<T> {
    pub fn new() -> BiVector<T> {
        BiVector {
            left:  Vector::new(),
            right: Vector::new(),
        }
    }

    pub fn new_with_bits(bits: u8) -> BiVector<T> {
        assert!(bits > 0, "Number of bits for the bivector must be positive");

        BiVector {
            left:  Vector::new_with_bits(bits),
            right: Vector::new_with_bits(bits),
        }
    }

    pub fn first(&self) -> Option<&T> {
        if self.left.len() > 0 {
            self.left.last()
        } else {
            self.right.first()
        }
    }

    pub fn last(&self) -> Option<&T> {
        if self.right.len() > 0 {
            self.right.last()
        } else {
            self.left.first()
        }
    }

    fn index_mapping(&self, index: usize) -> Option<IndexMapping> {
        if index >= self.len() {
            None
        } else if index < self.left.len() {
            Some(IndexMapping::Left(self.left.len() - index - 1))
        } else {
            Some(IndexMapping::Right(index - self.left.len()))
        }
    }

    /// Apply some operation on the left/right based on the given index.
    fn apply<'a, U, F: Fn(&'a Vector<T>, usize) -> U>(&'a self, index: usize, f: F) -> Option<U> {
        self.index_mapping(index).map(|m|
            match m {
                IndexMapping::Left(i)  => f(&self.left, i),
                IndexMapping::Right(i) => f(&self.right, i),
            }
        )
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        self.apply(index, |vector, i| vector.get(i).unwrap())
    }

    pub fn set(&self, index: usize, v: T) -> Option<BiVector<T>> {
        self.index_mapping(index).map(|index_mapping| {
            match index_mapping {
                IndexMapping::Left(i)  =>
                    BiVector {
                        left:  self.left.set(i, v).unwrap(),
                        right: self.right.clone(),
                    },
                IndexMapping::Right(i) =>
                    BiVector {
                        left:  self.left.clone(),
                        right: self.right.set(i, v).unwrap(),
                    },
            }
        })
    }

    pub fn push_back(&self, v: T) -> BiVector<T> {
        BiVector {
            left:  self.left.clone(),
            right: self.right.push(v),
        }
    }

    pub fn push_front(&self, v: T) -> BiVector<T> {
        BiVector {
            left:  self.left.push(v),
            right: self.right.clone(),
        }
    }

    pub fn len(&self) -> usize {
        self.left.len() + self.right.len()
    }

    /*
    pub fn iter(&self) -> impl Iterator<Item=T> {
        let x = self.left.iter().rev().chain(self.right.iter());
    }
    */
}

// WIP test iterator is exact size and is doubleended.

/*
pub struct Iter<T> {
    x: T
}
*/

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_first_last() -> () {
        let bivector: BiVector<i32> = BiVector::new()
            .push_back(0)
            .push_back(1)
            .push_front(-1)
            .push_back(2)
            .push_front(-2);
        let bivector_only_left: BiVector<i32> = BiVector::new()
            .push_front(-1)
            .push_front(-2);
        let bivector_only_right: BiVector<i32> = BiVector::new()
            .push_back(0)
            .push_back(1)
            .push_back(2);

        assert_eq!(bivector.first(), Some(&-2));
        assert_eq!(bivector.last(), Some(&2));

        assert_eq!(bivector_only_left.first(), Some(&-2));
        assert_eq!(bivector_only_left.last(), Some(&-1));

        assert_eq!(bivector_only_right.first(), Some(&0));
        assert_eq!(bivector_only_right.last(), Some(&2));
    }

    #[test]
    fn test_get() -> () {
        let bivector: BiVector<i32> = BiVector::new()
            .push_back(0)
            .push_back(1)
            .push_front(-1)
            .push_back(2)
            .push_front(-2);
        let bivector_only_left: BiVector<i32> = BiVector::new()
            .push_front(-1)
            .push_front(-2);
        let bivector_only_right: BiVector<i32> = BiVector::new()
            .push_back(0)
            .push_back(1)
            .push_back(2);

        assert_eq!(bivector.get(0), Some(&-2));
        assert_eq!(bivector.get(1), Some(&-1));
        assert_eq!(bivector.get(3), Some(&1));
        assert_eq!(bivector.get(4), Some(&2));
        assert_eq!(bivector.get(5), None);

        assert_eq!(bivector_only_left.get(0), Some(&-2));
        assert_eq!(bivector_only_left.get(1), Some(&-1));
        assert_eq!(bivector_only_left.get(2), None);

        assert_eq!(bivector_only_right.get(0), Some(&0));
        assert_eq!(bivector_only_right.get(1), Some(&1));
        assert_eq!(bivector_only_right.get(2), Some(&2));
        assert_eq!(bivector_only_right.get(3), None);
    }

    #[test]
    fn test_set() -> () {
        let bivector: BiVector<i32> = BiVector::new()
            .push_back(0)
            .push_back(1)
            .push_front(-1)
            .push_back(2)
            .push_front(-2);
        let bivector_only_left: BiVector<i32> = BiVector::new()
            .push_front(-1)
            .push_front(-2);
        let bivector_only_right: BiVector<i32> = BiVector::new()
            .push_back(0)
            .push_back(1)
            .push_back(2);

        assert_eq!(bivector.set(0, 10).unwrap().get(0), Some(&10));
        assert_eq!(bivector.set(1, 11).unwrap().get(1), Some(&11));
        assert_eq!(bivector.set(3, 13).unwrap().get(3), Some(&13));
        assert_eq!(bivector.set(4, 14).unwrap().get(4), Some(&14));
        assert!(bivector.set(5, 0).is_none());

        assert_eq!(bivector_only_left.set(0, 10).unwrap().get(0), Some(&10));
        assert_eq!(bivector_only_left.set(1, 11).unwrap().get(1), Some(&11));
        assert!(bivector_only_left.set(2, 0).is_none());

        assert_eq!(bivector_only_right.set(0, 10).unwrap().get(0), Some(&10));
        assert_eq!(bivector_only_right.set(1, 11).unwrap().get(1), Some(&11));
        assert_eq!(bivector_only_right.set(2, 12).unwrap().get(2), Some(&12));
        assert!(bivector_only_right.set(3, 0).is_none());
    }
}
