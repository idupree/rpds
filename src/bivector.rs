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
            left: Vector::new(),
            right: Vector::new(),
        }
    }

    pub fn new_with_bits(bits: u8) -> BiVector<T> {
        assert!(bits > 0, "Number of bits for the bivector must be positive");

        BiVector {
            left: Vector::new_with_bits(bits),
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
        match self.index_mapping(index) {
            Some(IndexMapping::Left(i))  =>
                Some(BiVector {
                    left:  self.left.set(i, v).unwrap(),
                    right: self.right.clone(),
                }),
            Some(IndexMapping::Right(i)) =>
                Some(BiVector {
                    left:  self.left.clone(),
                    right: self.right.set(i, v).unwrap(),
                }),
            None => None,
        }
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

    /* WIP
    pub fn iter(&self) -> Iter<T> {
        unimplemented!()
    }
    */
}
