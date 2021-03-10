use std::fmt;

use mgc::{Gc, Trace};
use parking_lot::{Mutex, const_mutex};
use rand::prelude::*;

struct Node<T> {
    value: T,
    next: Mutex<Option<Gc<Node<T>>>>,
    prev: Mutex<Option<Gc<Node<T>>>>,
}

impl<T: Trace> Trace for Node<T> {
    fn trace(&self) {
        let Self {value, next, prev} = self;
        value.trace();
        next.trace();
        prev.trace();
    }
}

impl<T: fmt::Debug> fmt::Debug for Node<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.value, f)?;
        if let Some(next) = self.next.lock().as_ref() {
            write!(f, "<->{:?}", next)?;
        }
        Ok(())
    }
}

impl<T> Node<T> {
    pub const fn new(value: T) -> Self {
        Self {
            value,
            next: const_mutex(None),
            prev: const_mutex(None),
        }
    }

    pub fn value(&self) -> &T {
        &self.value
    }
}

impl<T: Trace> Node<T> {
    pub fn remove(&self) {
        let mut prev = self.prev.lock().take();
        let mut next = self.next.lock().take();

        if let Some(prev) = prev.as_mut() {
            *prev.next.lock() = next.clone();
        }

        if let Some(next) = next.as_mut() {
            *next.prev.lock() = prev.clone();
        }
    }
}

/// A doubly-linked list
pub struct LinkedList<T> {
    head: Option<Gc<Node<T>>>,
    tail: Option<Gc<Node<T>>>,
    len: usize,
}

impl<T: Trace> Trace for LinkedList<T> {
    fn trace(&self) {
        let Self {head, tail, len: _} = self;
        head.trace();
        tail.trace();
    }
}

impl<T> Default for LinkedList<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: fmt::Debug> fmt::Debug for LinkedList<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        if let Some(head) = &self.head {
            fmt::Debug::fmt(head, f)?;
        }
        write!(f, "]")
    }
}

impl<T> LinkedList<T> {
    pub const fn new() -> Self {
        Self {
            head: None,
            tail: None,
            len: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }
}

impl<T: Trace> LinkedList<T> {
    pub fn front(&self) -> Option<&T> {
        self.head.as_ref().map(|node| node.value())
    }

    pub fn back(&self) -> Option<&T> {
        self.tail.as_ref().map(|node| node.value())
    }

    pub fn push_front(&mut self, value: T) {
        let node = Gc::new(Node::new(value));

        if let Some(head) = &self.head {
            *head.prev.lock() = Some(node.clone());
            *node.next.lock() = Some(head.clone());
        }

        if self.tail.is_none() {
            self.tail = Some(node.clone());
        }

        self.head = Some(node);

        self.len += 1;
    }

    pub fn push_back(&mut self, value: T) {
        let node = Gc::new(Node::new(value));

        if let Some(tail) = &self.tail {
            *tail.next.lock() = Some(node.clone());
            *node.prev.lock() = Some(tail.clone());
        }

        if self.head.is_none() {
            self.head = Some(node.clone());
        }

        self.tail = Some(node);

        self.len += 1;
    }

    pub fn pop_front(&mut self) {
        if let Some(head) = &self.head {
            if let Some(tail) = &self.tail {
                if Gc::ptr_eq(head, tail) {
                    self.tail = None;
                }
            }

            let next_head = head.next.lock().clone();
            head.remove();

            self.head = next_head;
            self.len -= 1;
        }
    }

    pub fn pop_back(&mut self) {
        if let Some(tail) = &self.tail {
            if let Some(head) = &self.head {
                if Gc::ptr_eq(head, tail) {
                    self.head = None;
                }
            }

            let next_tail = tail.prev.lock().clone();
            tail.remove();

            self.tail = next_tail;
            self.len -= 1;
        }
    }
}

#[test]
fn test_linked_list() {
    #[cfg(miri)]
    const OPERATIONS: usize = 500;
    #[cfg(not(miri))]
    const OPERATIONS: usize = 10_000;

    // Use when debugging this test
    const DEBUG: bool = false;

    macro_rules! dprint {
        ($($t:tt)*) => {
            if DEBUG {
                print!($($t)*);
            }
        };
    }

    macro_rules! dprintln {
        ($($t:tt)*) => {
            if DEBUG {
                println!($($t)*);
            }
        };
    }

    let seed: u64 = thread_rng().gen();
    println!("Seed: {}", seed);
    let mut rng = StdRng::seed_from_u64(seed);

    let mut list: LinkedList<i64> = LinkedList::new();
    for _ in 0..OPERATIONS {
        // Stress test GC by performing mark/sweep every iteration
        list.trace();
        mgc::sweep();

        match rng.gen_range(1..=100) {
            1..=25 => {
                let value = rng.gen_range(1..=OPERATIONS as i64);
                dprint!("PUSH FRONT {}", value);
                list.push_front(value);
                assert_eq!(list.front(), Some(&value));
                dprintln!(" ({:?})", list);
            },

            26..=50 => {
                let value = rng.gen_range(1..=OPERATIONS as i64);
                dprint!("PUSH BACK {}", value);
                list.push_back(value);
                assert_eq!(list.back(), Some(&value));
                dprintln!(" ({:?})", list);
            },

            51..=75 => {
                dprint!("POP FRONT {:?}", list.front());
                list.pop_front();
                dprintln!(" ({:?})", list);
            },

            76..=100 => {
                dprint!("POP BACK {:?}", list.back());
                list.pop_back();
                dprintln!(" ({:?})", list);
            },

            _ => unreachable!(),
        }
    }
}
