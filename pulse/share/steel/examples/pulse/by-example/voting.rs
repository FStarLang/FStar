pub fn read(p: (), s: (), arr: &mut [u32], len: usize, i: usize) -> u32 {
    arr[i]
}
//majorityrust$
pub fn majority<A: Clone + Copy + PartialEq>(
    p: (),
    s: (),
    votes: &mut [A],
    len: usize,
) -> std::option::Option<A> {
    let mut i = 1;
    let mut k = 1;
    let votes_0 = votes[0];
    let mut cand = votes_0;
    while {
        let vi = i;
        vi < len
    } {
        let vi = i;
        let vk = k;
        let vcand = cand;
        let votes_i = votes[vi];
        if vk == 0 {
            cand = votes_i;
            k = 1;
            i = vi + 1
        } else if votes_i == vcand {
            k = vk + 1;
            i = vi + 1
        } else {
            k = vk - 1;
            i = vi + 1
        };
    }
    let vk = k;
    let vcand = cand;
    let _bind_c = if vk == 0 {
        None
    } else if len < 2 * vk {
        Some(vcand)
    } else {
        i = 0;
        k = 0;
        while {
            let vi = i;
            vi < len
        } {
            let vi = i;
            let vk1 = k;
            let votes_i = votes[vi];
            if votes_i == vcand {
                k = vk1 + 1;
                i = vi + 1
            } else {
                i = vi + 1
            };
        }
        let vk1 = k;
        if len < 2 * vk1 {
            Some(vcand)
        } else {
            None
        }
    };
    let cand1 = _bind_c;
    let k1 = cand1;
    let i1 = k1;
    i1
}
//majorityrustend$

pub type u32_t = u32;
pub fn majority_mono(p: (), s: (), votes: &mut [u32_t], len: usize) -> std::option::Option<u32_t> {
    majority((), (), votes, len)
}

//majorityrusttest$
#[derive(Copy, Clone, PartialEq, Debug)]
enum Candidate {
    A,
    B,
    C,
}

#[test]
fn test() {
    let mut votes = [0, 1, 0, 0, 0, 1];
    let winner = majority((), (), &mut votes, 6);
    assert_eq!(winner, Some(0));

    let mut str_votes = ["a", "b", "a", "a", "c"];
    let str_winner = majority((), (), &mut str_votes, 5);
    assert_eq!(str_winner, Some("a"));

    let mut cand_votes = [Candidate::A, Candidate::B, Candidate::C, Candidate::B];
    let cand_winner = majority((), (), &mut cand_votes, 4);
    assert_eq!(cand_winner, None);
}
//majorityrusttestend$
