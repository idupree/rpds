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

use vector;
use vector::Vector;
use std::iter;

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

    pub fn iter(&self) -> Iter<T> {
        Iter::new(self)
    }
}

// WIP test iterator is exact size and is doubleended.

pub struct Iter<'a, T: 'a> {
    iter: iter::Chain<iter::Rev<vector::Iter<'a, T>>, vector::Iter<'a, T>>,
    length: usize,
}

impl<'a, T> Iter<'a, T> {
    fn new(bivector: &BiVector<T>) -> Iter<T> {
        Iter {
            iter: bivector.left.iter().rev().chain(bivector.right.iter()),
            length: bivector.len(),
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        if self.length > 0 {
            self.length -= 1;
        }
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.length;

        (len, Some(len))
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<&'a T> {
        if self.length > 0 {
            self.length -= 1;
        }
        self.iter.next_back()
    }
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_first_last() -> () {
        let vector: BiVector<i32> = BiVector::new()
            .push_back(0)
            .push_back(1)
            .push_front(-1)
            .push_back(2)
            .push_front(-2);
        let vector_only_left: BiVector<i32> = BiVector::new()
            .push_front(-1)
            .push_front(-2);
        let vector_only_right: BiVector<i32> = BiVector::new()
            .push_back(0)
            .push_back(1)
            .push_back(2);

        assert_eq!(vector.first(), Some(&-2));
        assert_eq!(vector.last(),  Some(&2));

        assert_eq!(vector_only_left.first(), Some(&-2));
        assert_eq!(vector_only_left.last(),  Some(&-1));

        assert_eq!(vector_only_right.first(), Some(&0));
        assert_eq!(vector_only_right.last(),  Some(&2));
    }

    #[test]
    fn test_get() -> () {
        let vector: BiVector<i32> = BiVector::new()
            .push_back(0)
            .push_back(1)
            .push_front(-1)
            .push_back(2)
            .push_front(-2);
        let vector_only_left: BiVector<i32> = BiVector::new()
            .push_front(-1)
            .push_front(-2);
        let vector_only_right: BiVector<i32> = BiVector::new()
            .push_back(0)
            .push_back(1)
            .push_back(2);

        assert_eq!(vector.get(0), Some(&-2));
        assert_eq!(vector.get(1), Some(&-1));
        assert_eq!(vector.get(3), Some(&1));
        assert_eq!(vector.get(4), Some(&2));
        assert_eq!(vector.get(5), None);

        assert_eq!(vector_only_left.get(0), Some(&-2));
        assert_eq!(vector_only_left.get(1), Some(&-1));
        assert_eq!(vector_only_left.get(2), None);

        assert_eq!(vector_only_right.get(0), Some(&0));
        assert_eq!(vector_only_right.get(1), Some(&1));
        assert_eq!(vector_only_right.get(2), Some(&2));
        assert_eq!(vector_only_right.get(3), None);
    }

    #[test]
    fn test_set() -> () {
        let vector: BiVector<i32> = BiVector::new()
            .push_back(0)
            .push_back(1)
            .push_front(-1)
            .push_back(2)
            .push_front(-2);
        let vector_only_left: BiVector<i32> = BiVector::new()
            .push_front(-1)
            .push_front(-2);
        let vector_only_right: BiVector<i32> = BiVector::new()
            .push_back(0)
            .push_back(1)
            .push_back(2);

        assert_eq!(vector.set(0, 10).unwrap().get(0), Some(&10));
        assert_eq!(vector.set(1, 11).unwrap().get(1), Some(&11));
        assert_eq!(vector.set(3, 13).unwrap().get(3), Some(&13));
        assert_eq!(vector.set(4, 14).unwrap().get(4), Some(&14));
        assert!(vector.set(5, 0).is_none());

        assert_eq!(vector_only_left.set(0, 10).unwrap().get(0), Some(&10));
        assert_eq!(vector_only_left.set(1, 11).unwrap().get(1), Some(&11));
        assert!(vector_only_left.set(2, 0).is_none());

        assert_eq!(vector_only_right.set(0, 10).unwrap().get(0), Some(&10));
        assert_eq!(vector_only_right.set(1, 11).unwrap().get(1), Some(&11));
        assert_eq!(vector_only_right.set(2, 12).unwrap().get(2), Some(&12));
        assert!(vector_only_right.set(3, 0).is_none());
    }

    #[test]
    fn test_iter_empty_vector() -> () {
        let bivector: BiVector<i32> = BiVector::new();

        for _ in bivector.iter() {
            panic!("iterator should be empty");
        }
    }

    #[test]
    fn test_iter_big_vector() -> () {
        let vector: BiVector<i32> = BiVector::new()
            .push_back(0)
            .push_back(1)
            .push_front(-1)
            .push_back(2)
            .push_front(-2);
        let mut left = 5;
        let mut expected = -2;

        for v in vector.iter() {
            left -= 1;

            assert!(left >= 0);
            assert_eq!(*v, expected);

            expected += 1;
        }

        assert_eq!(left, 0);
    }

    #[test]
    fn test_iter_backwards() -> () {
        let vector = BiVector::new()
            .push_back(0)
            .push_back(1)
            .push_front(-1)
            .push_back(2)
            .push_front(-2);
        let mut expected = 2;
        let mut left = 5;

        for n in vector.iter().rev() {
            left -= 1;

            assert!(left >= 0);
            assert_eq!(*n, expected);

            expected -= 1;
        }

        assert_eq!(left, 0);
    }

    #[test]
    fn test_iter_both_directions() -> () {
        let vector = BiVector::new()
            .push_back(0)
            .push_back(1)
            .push_front(-1)
            .push_back(2)
            .push_front(-2);
        let mut iterator = vector.iter();

        assert_eq!(iterator.next(),      Some(&-2));
        assert_eq!(iterator.next_back(), Some(&2));
        assert_eq!(iterator.next_back(), Some(&1));
        assert_eq!(iterator.next(),      Some(&-1));
        assert_eq!(iterator.next(),      Some(&0));
        assert_eq!(iterator.next_back(), None);
        assert_eq!(iterator.next(),      None);
    }

    #[test]
    fn test_iter_size_hint() -> () {
        let vector = BiVector::new()
            .push_back(0)
            .push_back(1)
            .push_front(-1);
        let mut iterator = vector.iter();

        assert_eq!(iterator.size_hint(), (3, Some(3)));

        iterator.next();

        assert_eq!(iterator.size_hint(), (2, Some(2)));

        iterator.next_back();

        assert_eq!(iterator.size_hint(), (1, Some(1)));

        iterator.next_back();

        assert_eq!(iterator.size_hint(), (0, Some(0)));
    }
}
