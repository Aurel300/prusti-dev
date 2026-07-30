use prusti_contracts::*;
//use std::ops::BitAnd;

//  #[derive(Debug, PartialEq)]
//  struct BooleanVector(Vec<bool>);

//  impl BitAnd for BooleanVector {
//      type Output = Self;

//      fn bitand(self, Self(rhs): Self) -> Self::Output {
//          let Self(lhs) = self;
//          assert_eq!(lhs.len(), rhs.len());
//          Self(
//              lhs.iter()
//                  .zip(rhs.iter())
//                  .map(|(x, y)| *x & *y)
//                  .collect()
//          )
//      }
//  }

//  fn two() {
//  let bv1 = BooleanVector(vec![true, true, false, false]);
//  let bv2 = BooleanVector(vec![true, false, true, false]);
//  let expected = BooleanVector(vec![true, false, false, false]);
//  assert_eq!(bv1 & bv2, expected);

//  }

// fn test() {
//     let v = vec![true, false, true];
// }

fn test() {
    let boxed_array: Box<[i32; 3]> = Box::new([1, 2, 3]);
    // let tmp = &[1,2,3];
    let boxed_slice: Box<[i32]> = boxed_array;
    assert_eq!(&*boxed_slice, &[1, 2, 3]);
}

// fn test(x: &[i32; 3]) {
//     let y: &[i32] = x;
// }
