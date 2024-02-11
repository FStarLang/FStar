mod dpe_;
mod pulsetutorial_algorithms;
// mod pulsetutorial_array;
mod pulsetutorial_loops;
#[cfg(test)]
use pulsetutorial_algorithms::*;
#[cfg(test)]
// use pulsetutorial_array::*;
#[cfg(test)]
use pulsetutorial_loops::*;

#[cfg(test)]
mod tests {
    use super::*;

    // #[test]
    // fn array_tests() {
    //     let mut v1 = vec![1, 2, 3];
    //     let mut v2 = vec![4, 5, 6];
    //     assert_eq!(compare((), (), &mut v1, &mut v2, 3, (), ()), false);
    //     let mut v3 = vec![1, 2, 3, 4];
    //     assert_eq!(compare((), (), &mut v1, &mut v3, 3, (), ()), true);
    //     copy(&mut v1, &mut v2, 3, (), (), ());
    //     assert_eq!(compare((), (), &mut v1, &mut v2, 3, (), ()), true);
    //     let mut v4 = [0; 2];
    //     assert_eq!(compare((), (), &mut v1, &mut v4, 2, (), ()), false);
    // }

    #[test]
    fn loop_tests() {
        assert_eq!(multiply_by_repeated_addition(3, 4), 12);
        assert_eq!(fib_loop(5), 8);
    }

    #[derive(Debug, PartialEq, Copy, Clone)]
    enum Cand {
        A,
        B,
        C,
        D,
    }

    #[test]
    fn voting_tests() {
        let mut votes = vec![
            Cand::B,
            Cand::A,
            Cand::C,
            Cand::A,
            Cand::D,
            Cand::A,
            Cand::A,
            Cand::A,
        ];
        assert_eq!(majority((), (), &mut votes, 8), Some(Cand::A));
        let mut votes1 = vec![Cand::A, Cand::B, Cand::A, Cand::D];
        assert_eq!(majority((), (), &mut votes1, 4), None);
    }
}
