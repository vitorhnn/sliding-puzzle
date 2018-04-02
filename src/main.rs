extern crate nalgebra as na;

use std::collections::HashSet;
use std::collections::BinaryHeap;
use std::cmp::Ordering;
use std::io;
use na::{Matrix3};

#[derive(Debug, Clone, Eq, PartialEq)]
enum Direction {
    Up,
    Down,
    Left,
    Right,
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct BoardState {
    board: Matrix3<i8>,
    steps: Vec<Direction>,
    zeropos: (usize, usize),
    weight: usize,
}

fn find_zero(mtx: &Matrix3<i8>) -> (usize, usize) {
    for j in 0..mtx.ncols() {
        for i in 0..mtx.nrows() {
            if mtx[(i, j)] == 0 {
                return (i, j);
            }
        }
    }

    panic!("passed matrix with no zero");
}

impl BoardState {
    fn new(board: Matrix3<i8>) -> BoardState {
        let steps = Vec::new();

        BoardState { board, steps, zeropos: find_zero(&board), weight: 1 }
    }

    fn up(&self, goal: &Matrix3<i8>) -> Option<BoardState> {
        let mut change = self.clone();

        match change.zeropos.0 {
            0 => None,
            _ => {
                let mut newpos = change.zeropos;
                newpos.0 -= 1;
                change.board.swap(change.zeropos, newpos);
                change.zeropos = newpos;
                change.steps.push(Direction::Up);
                change.weight = grand_sum(&(change.board - goal).abs()) as usize + change.steps.len();
                Some(change)
            },
        }
    }

    fn down(&self, goal: &Matrix3<i8>) -> Option<BoardState> {
        let mut change = self.clone();

        match change.zeropos.0 {
            2 => None,
            _ => {
                let mut newpos = change.zeropos;
                newpos.0 += 1;
                change.board.swap(change.zeropos, newpos);
                change.zeropos = newpos;
                change.steps.push(Direction::Down);
                change.weight = grand_sum(&(change.board - goal).abs()) as usize + change.steps.len();
                Some(change)
            }
        }
    }

    fn left(&self, goal: &Matrix3<i8>) -> Option<BoardState> {
        let mut change = self.clone();

        match change.zeropos.1 {
            0 => None,
            _ => {
                let mut newpos = change.zeropos;
                newpos.1 -= 1;
                change.board.swap(change.zeropos, newpos);
                change.zeropos = newpos;
                change.steps.push(Direction::Left);
                change.weight = grand_sum(&(change.board - goal).abs()) as usize + change.steps.len();
                Some(change)
            },
        }
    }

    fn right(&self, goal: &Matrix3<i8>) -> Option<BoardState> {
        let mut change = self.clone();

        match change.zeropos.1 {
            2 => None,
            _ => {
                let mut newpos = change.zeropos;
                newpos.1 += 1;
                change.board.swap(change.zeropos, newpos);
                change.zeropos = newpos;
                change.steps.push(Direction::Right);
                change.weight = grand_sum(&(change.board - goal).abs()) as usize + change.steps.len();
                Some(change)
            },
        }
    }
}

impl Ord for BoardState {
    fn cmp(&self, other: &BoardState) -> Ordering {
        other.weight.cmp(&self.weight)
    }
}

impl PartialOrd for BoardState {
    fn partial_cmp(&self, other: &BoardState) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

fn grand_sum(mtx: &Matrix3<i8>) -> i8 {
    let mut sum = 0;
    for j in 0..mtx.ncols() {
        for i in 0..mtx.nrows() {
            sum += mtx[(i, j)];
        }
    }

    return sum;
}

fn push_if_unique(state: BoardState, heap: &mut BinaryHeap<BoardState>, explored: &mut HashSet<Matrix3<i8>>) {
    if explored.insert(state.board) {
        heap.push(state);
    }
}

fn solve_sliding(initial_state: BoardState, goal: Matrix3<i8>) -> Option<BoardState> {
    let mut heap = BinaryHeap::new();
    let mut explored = HashSet::new();

    explored.insert(initial_state.board);
    heap.push(initial_state);

    let mut maybe_head = heap.pop();
    while maybe_head.is_some() {
        let head = maybe_head.unwrap();

        if head.board == goal {
            return Some(head);
        }

        head.up(&goal).and_then(|x| Some(push_if_unique(x, &mut heap, &mut explored)));
        head.down(&goal).and_then(|x| Some(push_if_unique(x, &mut heap, &mut explored)));
        head.left(&goal).and_then(|x| Some(push_if_unique(x, &mut heap, &mut explored)));
        head.right(&goal).and_then(|x| Some(push_if_unique(x, &mut heap, &mut explored)));


        maybe_head = heap.pop();
    }

    None
}

macro_rules! parse_line {
    ($($t: ty),+) => ({
        let mut a_str = String::new();
        io::stdin().read_line(&mut a_str).expect("read error");
        let mut a_iter = a_str.split_whitespace();
        (
            $(
            a_iter.next().unwrap().parse::<$t>().expect("parse error"),
            )+
        )
    })
}

fn main() {
    let goal = Matrix3::new(0, 1, 2,
                            3, 4, 5,
                            6, 7, 8);

    let (a0, a1, a2) = parse_line!(i8, i8, i8);
    let (a3, a4, a5) = parse_line!(i8, i8, i8);
    let (a6, a7, a8) = parse_line!(i8, i8, i8);

    let start = Matrix3::new(a0, a1, a2,
                             a3, a4, a5,
                             a6, a7, a8);

    let start_state = BoardState::new(start);
    let maybe_solution = solve_sliding(start_state, goal);

    if let Some(solution) = maybe_solution {
        println!("{:?}", solution.steps);
        println!("{}", solution.steps.len());
    }
}
