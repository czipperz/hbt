use std::fmt;

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
enum Balance {
    Left, Middle, Right,
}

#[derive(PartialEq, Eq, Clone)]
pub struct HeightBalancedTree<T> {
    root: Option<Box<Node<T>>>,
}

#[derive(PartialEq, Eq, Clone)]
struct Node<T> {
    left: Option<Box<Node<T>>>,
    right: Option<Box<Node<T>>>,
    balance: Balance,
    data: T,
}

fn format_node_<T: fmt::Debug>(node: &Node<T>, formatter: &mut fmt::Formatter, depth: usize) -> fmt::Result {
    use std::fmt::Write;
    try!(format_node(&node.right, formatter, depth + 1));
    for _ in 0..depth {
        try!(formatter.write_char(' '));
        try!(formatter.write_char(' '));
    }
    try!(node.data.fmt(formatter));
    try!(formatter.write_char('\n'));
    try!(format_node(&node.left, formatter, depth + 1));
    Ok(())
}

fn format_node<T: fmt::Debug>(node: &Option<Box<Node<T>>>, formatter: &mut fmt::Formatter, depth: usize) -> fmt::Result {
    match node {
        &Some(ref node) => format_node_(node, formatter, depth),
        _ => Ok(()),
    }
}

impl<T: fmt::Debug> fmt::Debug for Node<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        format_node_(self, formatter, 0)
    }
}

impl<T: fmt::Debug> fmt::Debug for HeightBalancedTree<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        format_node(&self.root, formatter, 0)
    }
}

fn height<T>(nullable: &Option<Box<Node<T>>>) -> isize {
    match nullable {
        &Some(ref node) =>
            match node.balance {
                Balance::Left => 1 + height(&node.left),
                _ => 1 + height(&node.right),
            },
        _ => -1,
    }
}

fn size<T>(nullable: &Option<Box<Node<T>>>) -> usize {
    match nullable {
        &Some(ref node) =>
            size(&node.left) + 1 + size(&node.right),
        _ => 0,
    }
}

fn contains<T: Ord>(nullable: &Option<Box<Node<T>>>, data: &T) -> bool {
    match nullable {
        &Some(ref node) => {
            if *data < node.data {
                contains(&node.left, data)
            } else if *data > node.data {
                contains(&node.right, data)
            } else {
                true
            }
        },
        &None => false,
    }
}

/// Rotations
fn single_right<T>(a: &mut Box<Node<T>>) {
    let mut b = a.left.take().unwrap();
    if b.balance == Balance::Left {
        a.balance = Balance::Middle;
        b.balance = Balance::Middle;
    } else {
        //     A
        //   B    T2h-1
        // T0h T1h
        //
        //     B
        // T0h    A
        //     T1h  T2h-1
        a.balance = Balance::Left;
        b.balance = Balance::Right;
    }
    a.left = b.right.take();
    std::mem::swap(a, &mut b);
    a.right = Some(b);
}

fn single_left<T>(a: &mut Box<Node<T>>) {
    let mut b = a.right.take().unwrap();
    if b.balance == Balance::Right {
        a.balance = Balance::Middle;
        b.balance = Balance::Middle;
    } else {
        //     A
        // T0h-1  B
        //     T1h T2h
        //
        //         B
        //     A      T2h
        // T0h-1 T1h
        a.balance = Balance::Right;
        b.balance = Balance::Left;
    }
    a.right = b.left.take();
    std::mem::swap(a, &mut b);
    a.left = Some(b);
}

fn double_right<T>(top: &mut Box<Node<T>>) {
    let mut left = top.left.take().unwrap();
    let mut left_right = left.right.take().unwrap();
    //         AX
    //     B\       T3h
    // T0h   C/
    //     T1h T2h-1
    // --------
    //         C=
    //    B=        A\
    // T0h T1h  T2h-1 T3h
    std::mem::swap(top, &mut left_right);
    let mut a = left_right;
    let mut b = left;
    let mut c = top;
    if c.balance == Balance::Left {
        a.balance = Balance::Right;
        b.balance = Balance::Middle;
    } else if c.balance == Balance::Right {
        a.balance = Balance::Middle;
        b.balance = Balance::Left;
    } else {
        a.balance = Balance::Middle;
        b.balance = Balance::Middle;
    }
    c.balance = Balance::Middle;

    a.left = c.right.take();
    c.right = Some(a);
    b.right = c.left.take();
    c.left = Some(b);
}

fn double_left<T>(top: &mut Box<Node<T>>) {
    let mut right = top.right.take().unwrap();
    let mut right_left = right.left.take().unwrap();
    //      AX
    // T0h       B/
    //        C/    T3h
    //     T1h  T2h-1
    // -------
    //         C=
    //    A=        B\
    // T0h T1h  T2h-1 T3h
    std::mem::swap(top, &mut right_left);
    let mut a = right_left;
    let mut b = right;
    let mut c = top;
    if c.balance == Balance::Left {
        a.balance = Balance::Middle;
        b.balance = Balance::Right;
    } else if c.balance == Balance::Right {
        a.balance = Balance::Left;
        b.balance = Balance::Middle;
    } else {
        a.balance = Balance::Middle;
        b.balance = Balance::Middle;
    }
    c.balance = Balance::Middle;

    a.right = c.left.take();
    c.left = Some(a);
    b.left = c.right.take();
    c.right = Some(b);
}

/// Handling when to call rotations
fn shift_right<T>(node: &mut Box<Node<T>>) {
    match node.balance {
        Balance::Left => node.balance = Balance::Middle,
        Balance::Middle => node.balance = Balance::Right,
        Balance::Right =>
            if node.right.as_ref().unwrap().balance == Balance::Left {
                double_left(node);
            } else {
                single_left(node);
            },
    }
}

fn shift_left<T>(node: &mut Box<Node<T>>) {
    match node.balance {
        Balance::Left =>
            if node.left.as_ref().unwrap().balance == Balance::Right {
                double_right(node);
            } else {
                single_right(node);
            },
        Balance::Middle => node.balance = Balance::Left,
        Balance::Right => node.balance = Balance::Middle,
    }
}

/// Recursive implementation of insertion
fn insert<T: Ord>(nullable: &mut Option<Box<Node<T>>>, data: T) {
    if nullable.is_none() {
        *nullable = Some(Box::new(Node {
            left: None, right: None, balance: Balance::Middle, data }));
        return;
    }
    let mut node = nullable.take().unwrap();
    if data < node.data {
        let balance_before = node.left.as_ref().map(|right| right.balance);
        insert(&mut node.left, data);
        if balance_before == None ||
           balance_before == Some(Balance::Middle) && node.left.as_ref().unwrap().balance != Balance::Middle {
            shift_left(&mut node);
        }
    } else if data > node.data {
        let balance_before = node.right.as_ref().map(|right| right.balance);
        insert(&mut node.right, data);
        if balance_before == None ||
           balance_before == Some(Balance::Middle) && node.right.as_ref().unwrap().balance != Balance::Middle {
            shift_right(&mut node);
        }
    }
    *nullable = Some(node);
}

/// Handling what happens when we do a removal
fn remove_rebalance_left<T>(node: &mut Box<Node<T>>, balance_before: Balance) {
    if node.left.is_none() ||
        (balance_before != Balance::Middle &&
         node.left.as_ref().unwrap().balance == Balance::Middle) {
        shift_right(node);
    }
}

fn remove_rebalance_right<T>(node: &mut Box<Node<T>>, balance_before: Balance) {
    if node.right.is_none() ||
        (balance_before != Balance::Middle &&
         node.right.as_ref().unwrap().balance == Balance::Middle) {
        shift_left(node);
    }
}

fn remove_largest<T: Ord>(nullable: &mut Option<Box<Node<T>>>) -> T {
    if nullable.is_none() { unreachable!(); }
    let mut node = nullable.take().unwrap();
    if node.right.is_some() {
        let balance_before = node.right.as_ref().unwrap().balance.clone();
        let result = remove_largest(&mut node.right);
        remove_rebalance_right(&mut node, balance_before);
        *nullable = Some(node);
        result
    } else {
        let node = *node;
        *nullable = node.left;
        node.data
    }
}

/// This removes the root of the tree.  If there are two children, the
/// new root is the greatest item of the left subtree.
fn remove_root<T: Ord>(mut node: Box<Node<T>>) -> (T, Option<Box<Node<T>>>) {
    if node.left.is_none() && node.right.is_none() {
        (node.data, None)
    } else if node.left.is_none() {
        let node = *node;
        (node.data, node.right)
    } else if node.right.is_none() {
        let node = *node;
        (node.data, node.left)
    } else {
        let balance_before = node.left.as_ref().unwrap().balance;
        let largest = remove_largest(&mut node.left);
        remove_rebalance_left(&mut node, balance_before);
        let olddata = std::mem::replace(&mut node.data, largest);
        (olddata, Some(node))
    }
}

/// Recursive implementation of remove
fn remove<T: Ord>(nullable: &mut Option<Box<Node<T>>>, data: &T) {
    if nullable.is_none() { return; }
    let mut node = nullable.take().unwrap();
    if *data == node.data {
        *nullable = remove_root(node).1;
        return;
    } else if *data < node.data {
        if node.left.is_some() {
            let balance_before = node.left.as_ref().unwrap().balance.clone();
            remove(&mut node.left, data);
            remove_rebalance_left(&mut node, balance_before);
        }
    } else {
        if node.right.is_some() {
            let balance_before = node.right.as_ref().unwrap().balance.clone();
            remove(&mut node.right, data);
            remove_rebalance_right(&mut node, balance_before);
        }
    }
    *nullable = Some(node);
}

fn merge_left<T: Ord>(into: &mut Option<Box<Node<T>>>, out: Option<Box<Node<T>>>, mut depthtogo: isize) -> bool {
    if depthtogo >= 1 {
        let into = into.as_mut().unwrap();
        depthtogo -= if into.balance == Balance::Right { 2 } else { 1 };
        let shift = merge_left(&mut into.left, out, depthtogo);
        if shift {
            let is_middle = into.balance == Balance::Middle;
            shift_right(into);
            is_middle
        } else {
            false
        }
    } else {
        let (uninit, ninto) = remove_root(Box::new(Node {
            left: out,
            right: into.take(),
            balance: if depthtogo == 0 { Balance::Middle } else { Balance::Left },
            data: unsafe { std::mem::uninitialized() },
        }));
        *into = ninto;
        std::mem::forget(uninit);
        true
    }
}

fn merge_right<T: Ord>(into: &mut Option<Box<Node<T>>>, out: Option<Box<Node<T>>>, mut depthtogo: isize) -> bool {
    if depthtogo >= 1 {
        let into = into.as_mut().unwrap();
        depthtogo -= if into.balance == Balance::Left { 2 } else { 1 };
        let shift = merge_right(&mut into.right, out, depthtogo);
        if shift {
            let is_middle = into.balance == Balance::Middle;
            shift_left(into);
            is_middle
        } else {
            false
        }
    } else {
        let (uninit, ninto) = remove_root(Box::new(Node {
            left: into.take(),
            right: out,
            balance: if depthtogo == 0 { Balance::Middle } else { Balance::Right },
            data: unsafe { std::mem::uninitialized() },
        }));
        *into = ninto;
        std::mem::forget(uninit);
        true
    }
}

fn merge<T: Ord>(l: &mut Option<Box<Node<T>>>, mut r: Option<Box<Node<T>>>) {
    if !r.is_none() {
        if l.is_none() {
            *l = r;
        } else {
            let depthtogo = height(l) - height(&r);
            if depthtogo >= 0 {
                merge_right(l, r, depthtogo);
            } else {
                std::mem::swap(l, &mut r);
                merge_left(l, r, -depthtogo);
            }
        }
    }
}

fn split_off<T: Ord>(nullable: &mut Option<Box<Node<T>>>, data: &T) -> Option<Box<Node<T>>> {
    if nullable.is_none() {
        None
    } else {
        let node = *nullable.take().unwrap();
        let mut left = node.left;
        let mut right = node.right;
        let mut discarded;
        if *data < node.data {
            discarded = split_off(&mut left, data);
            insert(&mut right, node.data);
            merge(&mut discarded, right);
        } else if *data > node.data {
            discarded = split_off(&mut right, data);
            insert(&mut left, node.data);
            merge(&mut left, right);
        } else {
            insert(&mut right, node.data);
            discarded = right
        }
        *nullable = left;
        discarded
    }
}

pub struct Iter<'a, T: 'a> {
    stack: Vec<&'a Node<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.stack.is_empty() {
            None
        } else {
            let mut n = self.stack.pop().unwrap();
            let data = &n.data;
            if n.right.is_some() {
                n = n.right.as_ref().unwrap();
                self.stack.push(n);
                while n.left.is_some() {
                    n = n.left.as_ref().unwrap();
                    self.stack.push(n);
                }
            }
            Some(data)
        }
    }
}

impl<T> HeightBalancedTree<T> {
    pub fn new() -> Self {
        HeightBalancedTree { root: None }
    }

    pub fn height(&self) -> isize {
        height(&self.root)
    }

    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    pub fn size(&self) -> usize {
        size(&self.root)
    }

    pub fn iter(&self) -> Iter<T> {
        let mut stack = Vec::new();
        let mut n = &self.root;
        while n.is_some() {
            let u = n.as_ref().unwrap();
            stack.push(&**u);
            n = &u.left;
        }
        Iter { stack }
    }

    pub fn clear(&mut self) {
        self.root = None;
    }
}

impl<T: Ord> HeightBalancedTree<T> {
    pub fn insert(&mut self, data: T) {
        insert(&mut self.root, data);
    }

    pub fn remove(&mut self, data: &T) {
        remove(&mut self.root, data);
    }

    pub fn contains(&self, data: &T) -> bool {
        contains(&self.root, data)
    }

    pub fn split_off(&mut self, data: &T) -> HeightBalancedTree<T> {
        HeightBalancedTree { root: split_off(&mut self.root, data) }
    }
}

impl<T> Default for HeightBalancedTree<T> {
    fn default() -> Self {
        HeightBalancedTree::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn to_string<T: fmt::Debug>(nullable: &Option<Box<Node<T>>>) -> String {
        fn to_string_<T: fmt::Debug>(nullable: &Option<Box<Node<T>>>, depth: usize, s: &mut String) {
            match nullable {
                &Some(ref node) => {
                    to_string_(&node.right, depth + 1, s);
                    for _ in 0..depth {
                        s.push_str("  ");
                    }
                    s.push_str(&*format!("{:?} {:?}\n", node.balance, node.data));
                    to_string_(&node.left, depth + 1, s);
                },
                &None => (),
            }
        }
        let mut s = String::new();
        to_string_(nullable, 0, &mut s);
        s
    }

    fn build_node<T>(data: T) -> Option<Box<Node<T>>> {
        Some(Box::new(Node { left: None, right: None, balance: Balance::Middle, data }))
    }
    fn build_tree<T>(left: Option<Box<Node<T>>>, data: T, right: Option<Box<Node<T>>>, balance: Balance)
                     -> Option<Box<Node<T>>> {
        Some(Box::new(Node { left, right, balance, data }))
    }

    fn build_n0() -> HeightBalancedTree<i32> {
        HeightBalancedTree::<i32> {
            root: None,
        }
    }
    fn build_n1() -> HeightBalancedTree<i32> {
        HeightBalancedTree {
             root: build_tree(None, 3, None, Balance::Middle),
        }
    }
    fn build_n31() -> HeightBalancedTree<i32> {
        HeightBalancedTree {
            root:
            build_tree(
                build_tree(
                    build_tree(
                        build_tree(
                            build_tree(None, 1, None, Balance::Middle),
                            2,
                            build_tree(None, 3, None, Balance::Middle),
                            Balance::Middle),
                        4,
                        build_tree(
                            build_tree(None, 5, None, Balance::Middle),
                            6,
                            build_tree(None, 7, None, Balance::Middle),
                            Balance::Middle),
                        Balance::Middle),
                    8,
                    build_tree(
                        build_tree(
                            build_tree(None, 9, None, Balance::Middle),
                            10,
                            build_tree(None, 11, None, Balance::Middle),
                            Balance::Middle),
                        12,
                        build_tree(
                            build_tree(None, 13, None, Balance::Middle),
                            14,
                            build_tree(None, 15, None, Balance::Middle),
                            Balance::Middle),
                        Balance::Middle),
                    Balance::Middle),
                16,
                build_tree(
                    build_tree(
                        build_tree(
                            build_tree(None, 17, None, Balance::Middle),
                            18,
                            build_tree(None, 19, None, Balance::Middle),
                            Balance::Middle),
                        20,
                        build_tree(
                            build_tree(None, 21, None, Balance::Middle),
                            22,
                            build_tree(None, 23, None, Balance::Middle),
                            Balance::Middle),
                        Balance::Middle),
                    24,
                    build_tree(
                        build_tree(
                            build_tree(None, 25, None, Balance::Middle),
                            26,
                            build_tree(None, 27, None, Balance::Middle),
                            Balance::Middle),
                        28,
                        build_tree(
                            build_tree(None, 29, None, Balance::Middle),
                            30,
                            build_tree(None, 31, None, Balance::Middle),
                            Balance::Middle),
                        Balance::Middle),
                    Balance::Middle),
                Balance::Middle),
        }
    }

    fn slow_height<T>(nullable: &Option<Box<Node<T>>>) -> isize {
        match nullable {
            &Some(ref node) =>
                1 + std::cmp::max(slow_height(&node.left), slow_height(&node.right)),
            _ => -1,
        }
    }

    fn check_balances<T: fmt::Debug>(nullable: &Option<Box<Node<T>>>) {
        match nullable {
            &Some(ref node) => {
                check_balances(&node.left);
                check_balances(&node.right);
                let lefth = slow_height(&node.left);
                let righth = slow_height(&node.right);
                assert!(lefth <= righth + 1, "'{:?}'", node);
                assert!(righth <= lefth + 1, "'{:?}'", node);
                if lefth < righth {
                    assert_eq!(Balance::Right, node.balance, "'{:?}'", node);
                } else if lefth > righth {
                    assert_eq!(Balance::Left, node.balance, "'{:?}'", node);
                } else {
                    assert_eq!(Balance::Middle, node.balance, "'{:?}'", node);
                }
            },
            &None => ()
        }
    }

    fn get_node<'a, T: Ord>(nullable: &'a Option<Box<Node<T>>>, data: &T) -> &'a Option<Box<Node<T>>> {
        match nullable {
            &Some(ref node) => {
                if node.data == *data {
                    nullable
                } else if *data > node.data {
                    get_node(&node.right, data)
                } else {
                    get_node(&node.left, data)
                }
            },
            &None => nullable,
        }
    }

    #[test]
    fn iter_tests() {
        let tree = build_n31();
        let mut iter = tree.iter();
        for i in 1..32 {
            assert_eq!(i, *iter.next().unwrap());
        }
        assert!(iter.next().is_none());
    }

    #[test]
    fn n0_tree_queries() {
        let tree = build_n0();
        assert_eq!(-1, tree.height());
        assert_eq!(0, tree.size());
        assert!(!tree.contains(&3));
        assert!(!tree.contains(&0));
        assert!(!tree.contains(&-3));
    }

    #[test]
    fn n1_tree_queries() {
        let tree = build_n1();
        assert_eq!(0, tree.height());
        assert_eq!(1, tree.size());
        assert!(!tree.contains(&-3));
        assert!(!tree.contains(&1));
        assert!(tree.contains(&3));
    }

    #[test]
    fn n31_tree_queries() {
        let tree = build_n31();
        assert_eq!(4, tree.height());
        assert_eq!(31, tree.size());
        assert_eq!("        31
      30
        29
    28
        27
      26
        25
  24
        23
      22
        21
    20
        19
      18
        17
16
        15
      14
        13
    12
        11
      10
        9
  8
        7
      6
        5
    4
        3
      2
        1
", format!("{:?}", tree));
        assert!(tree.contains(&3));
        assert!(tree.contains(&30));
        assert!(!tree.contains(&0));
        assert!(!tree.contains(&-1));
        assert!(!tree.contains(&32));
    }

    #[test]
    fn n0_insertions() {
        let mut tree = build_n0();
        tree.insert(1);
        assert_eq!("1
", format!("{:?}", tree));
        check_balances(&tree.root);
        assert_eq!(Balance::Middle, tree.root.as_ref().unwrap().balance);

        tree.insert(2);
        assert_eq!("  2
1
", format!("{:?}", tree));
        check_balances(&tree.root);
        assert_eq!(Balance::Right, tree.root.as_ref().unwrap().balance);

        tree.insert(3);
        assert_eq!("  3
2
  1
", format!("{:?}", tree));
        check_balances(&tree.root);
        assert_eq!(Balance::Middle, tree.root.as_ref().unwrap().balance);
    }

    #[test]
    fn n31_insertions() {
        let mut tree = build_n31();
        tree.insert(32);
        assert_eq!("          32
        31
      30
        29
    28
        27
      26
        25
  24
        23
      22
        21
    20
        19
      18
        17
16
        15
      14
        13
    12
        11
      10
        9
  8
        7
      6
        5
    4
        3
      2
        1
", format!("{:?}", tree));
        check_balances(&tree.root);
        assert_eq!(Balance::Right, tree.root.as_ref().unwrap().balance);

        tree.insert(32);
        assert_eq!("          32
        31
      30
        29
    28
        27
      26
        25
  24
        23
      22
        21
    20
        19
      18
        17
16
        15
      14
        13
    12
        11
      10
        9
  8
        7
      6
        5
    4
        3
      2
        1
", format!("{:?}", tree));
        check_balances(&tree.root);

        tree.insert(33);
        assert_eq!("          33
        32
          31
      30
        29
    28
        27
      26
        25
  24
        23
      22
        21
    20
        19
      18
        17
16
        15
      14
        13
    12
        11
      10
        9
  8
        7
      6
        5
    4
        3
      2
        1
", format!("{:?}", tree));
        check_balances(&tree.root);

        tree.insert(0);
        assert_eq!("          33
        32
          31
      30
        29
    28
        27
      26
        25
  24
        23
      22
        21
    20
        19
      18
        17
16
        15
      14
        13
    12
        11
      10
        9
  8
        7
      6
        5
    4
        3
      2
        1
          0
", format!("{:?}", tree));
        check_balances(&tree.root);

        tree.insert(-3);
        assert_eq!("          33
        32
          31
      30
        29
    28
        27
      26
        25
  24
        23
      22
        21
    20
        19
      18
        17
16
        15
      14
        13
    12
        11
      10
        9
  8
        7
      6
        5
    4
        3
      2
          1
        0
          -3
", format!("{:?}", tree));
        check_balances(&tree.root);
        {
            let two_boxed = get_node(&tree.root, &2);
            let two = two_boxed.as_ref().unwrap();
            assert_eq!(Balance::Left, two.balance);
            assert_eq!(2, height(two_boxed));
            assert_eq!(Balance::Middle, two.left.as_ref().unwrap().balance);
            let n3_boxed = get_node(&tree.root, &-3);
            let n3 = n3_boxed.as_ref().unwrap();
            assert_eq!(Balance::Middle, n3.balance);
        }

        tree.insert(-1);
        assert_eq!("          33
        32
          31
      30
        29
    28
        27
      26
        25
  24
        23
      22
        21
    20
        19
      18
        17
16
        15
      14
        13
    12
        11
      10
        9
  8
        7
      6
        5
    4
          3
        2
          1
      0
          -1
        -3
", format!("{:?}", tree));
        check_balances(&tree.root);
        {
            let n3_boxed = get_node(&tree.root, &-3);
            let n3 = n3_boxed.as_ref().unwrap();
            assert_eq!(Balance::Right, n3.balance);
            let zero_boxed = get_node(&tree.root, &0);
            let zero = zero_boxed.as_ref().unwrap();
            assert_eq!(Balance::Middle, zero.balance);
        }

        tree.insert(-2);
        assert_eq!("          33
        32
          31
      30
        29
    28
        27
      26
        25
  24
        23
      22
        21
    20
        19
      18
        17
16
        15
      14
        13
    12
        11
      10
        9
  8
        7
      6
        5
    4
          3
        2
          1
      0
          -1
        -2
          -3
", format!("{:?}", tree));
        check_balances(&tree.root);
    }

    #[test]
    fn big_tree_1_insert() {
        let mut tree = HeightBalancedTree {
            root:
            build_tree(
                build_node(2),
                4,
                build_tree(
                    build_node(6),
                    8,
                    build_node(10),
                    Balance::Middle),
                Balance::Right,
            ),
        };
        check_balances(&tree.root);
        assert_eq!("    10
  8
    6
4
  2
", format!("{:?}", tree));
        check_balances(&tree.root);

        tree.insert(5);
        assert_eq!("    10
  8
6
    5
  4
    2
", format!("{:?}", tree));
        check_balances(&tree.root);

        tree.insert(12);
        assert_eq!("    12
  10
    8
6
    5
  4
    2
", format!("{:?}", tree));
        check_balances(&tree.root);

        tree.insert(13);
        assert_eq!("      13
    12
  10
    8
6
    5
  4
    2
", format!("{:?}", tree));
        check_balances(&tree.root);

        tree.insert(14);
        assert_eq!("      14
    13
      12
  10
    8
6
    5
  4
    2
", format!("{:?}", tree));
        check_balances(&tree.root);

        tree.insert(15);
        assert_eq!("      15
    14
  13
      12
    10
      8
6
    5
  4
    2
", format!("{:?}", tree));
        check_balances(&tree.root);

        tree.insert(16);
        assert_eq!("      16
    15
      14
  13
      12
    10
      8
6
    5
  4
    2
", format!("{:?}", tree));
        check_balances(&tree.root);

        tree.insert(17);
        assert_eq!("      17
    16
  15
    14
13
      12
    10
      8
  6
      5
    4
      2
", format!("{:?}", tree));
        check_balances(&tree.root);

        tree.insert(18);
        assert_eq!("      18
    17
      16
  15
    14
13
      12
    10
      8
  6
      5
    4
      2
", format!("{:?}", tree));
        check_balances(&tree.root);

        tree.insert(20);
        assert_eq!("      20
    18
  17
      16
    15
      14
13
      12
    10
      8
  6
      5
    4
      2
", format!("{:?}", tree));
        check_balances(&tree.root);

        tree.insert(19);
        assert_eq!("      20
    19
      18
  17
      16
    15
      14
13
      12
    10
      8
  6
      5
    4
      2
", format!("{:?}", tree));
        check_balances(&tree.root);
    }

    #[test]
    fn n0_remove() {
        let mut tree = build_n0();
        tree.remove(&20);
        assert_eq!("", format!("{:?}", tree));
        check_balances(&tree.root);
    }

    #[test]
    fn n1_remove() {
        let mut tree = build_n1();
        tree.remove(&20);
        assert_eq!("3
", format!("{:?}", tree));
        check_balances(&tree.root);

        tree.remove(&3);
        assert_eq!("", format!("{:?}", tree));
        check_balances(&tree.root);
    }

    #[test]
    fn n31_remove() {
        let mut tree = build_n31();
        assert_eq!("        31
      30
        29
    28
        27
      26
        25
  24
        23
      22
        21
    20
        19
      18
        17
16
        15
      14
        13
    12
        11
      10
        9
  8
        7
      6
        5
    4
        3
      2
        1
", format!("{:?}", tree));

        tree.remove(&9);
        assert_eq!("        31
      30
        29
    28
        27
      26
        25
  24
        23
      22
        21
    20
        19
      18
        17
16
        15
      14
        13
    12
        11
      10
  8
        7
      6
        5
    4
        3
      2
        1
", format!("{:?}", tree));
        check_balances(&tree.root);

        tree.remove(&20);
        assert_eq!("        Middle 31
      Middle 30
        Middle 29
    Middle 28
        Middle 27
      Middle 26
        Middle 25
  Middle 24
        Middle 23
      Middle 22
        Middle 21
    Middle 19
      Left 18
        Middle 17
Middle 16
        Middle 15
      Middle 14
        Middle 13
    Middle 12
        Middle 11
      Right 10
  Middle 8
        Middle 7
      Middle 6
        Middle 5
    Middle 4
        Middle 3
      Middle 2
        Middle 1
", to_string(&tree.root));
        check_balances(&tree.root);

        tree.remove(&17);
        assert_eq!("        Middle 31
      Middle 30
        Middle 29
    Middle 28
        Middle 27
      Middle 26
        Middle 25
  Middle 24
        Middle 23
      Middle 22
        Middle 21
    Right 19
      Middle 18
Middle 16
        Middle 15
      Middle 14
        Middle 13
    Middle 12
        Middle 11
      Right 10
  Middle 8
        Middle 7
      Middle 6
        Middle 5
    Middle 4
        Middle 3
      Middle 2
        Middle 1
", to_string(&tree.root));
        check_balances(&tree.root);

        tree.remove(&18);
        assert_eq!("        Middle 31
      Middle 30
        Middle 29
    Middle 28
        Middle 27
      Middle 26
        Middle 25
  Middle 24
      Middle 23
    Left 22
        Middle 21
      Right 19
Middle 16
        Middle 15
      Middle 14
        Middle 13
    Middle 12
        Middle 11
      Right 10
  Middle 8
        Middle 7
      Middle 6
        Middle 5
    Middle 4
        Middle 3
      Middle 2
        Middle 1
", to_string(&tree.root));
        check_balances(&tree.root);

        tree.remove(&19);
        assert_eq!("        Middle 31
      Middle 30
        Middle 29
    Middle 28
        Middle 27
      Middle 26
        Middle 25
  Right 24
      Middle 23
    Middle 22
      Middle 21
Middle 16
        Middle 15
      Middle 14
        Middle 13
    Middle 12
        Middle 11
      Right 10
  Middle 8
        Middle 7
      Middle 6
        Middle 5
    Middle 4
        Middle 3
      Middle 2
        Middle 1
", to_string(&tree.root));
        check_balances(&tree.root);

        tree.remove(&21);
        assert_eq!("        Middle 31
      Middle 30
        Middle 29
    Middle 28
        Middle 27
      Middle 26
        Middle 25
  Right 24
      Middle 23
    Right 22
Middle 16
        Middle 15
      Middle 14
        Middle 13
    Middle 12
        Middle 11
      Right 10
  Middle 8
        Middle 7
      Middle 6
        Middle 5
    Middle 4
        Middle 3
      Middle 2
        Middle 1
", to_string(&tree.root));
        check_balances(&tree.root);

        tree.remove(&22);
        assert_eq!("      Middle 31
    Middle 30
      Middle 29
  Left 28
        Middle 27
      Middle 26
        Middle 25
    Right 24
      Middle 23
Middle 16
        Middle 15
      Middle 14
        Middle 13
    Middle 12
        Middle 11
      Right 10
  Middle 8
        Middle 7
      Middle 6
        Middle 5
    Middle 4
        Middle 3
      Middle 2
        Middle 1
", to_string(&tree.root));
        check_balances(&tree.root);

        tree.remove(&4);
        assert_eq!("      Middle 31
    Middle 30
      Middle 29
  Left 28
        Middle 27
      Middle 26
        Middle 25
    Right 24
      Middle 23
Middle 16
        Middle 15
      Middle 14
        Middle 13
    Middle 12
        Middle 11
      Right 10
  Middle 8
        Middle 7
      Middle 6
        Middle 5
    Middle 3
      Left 2
        Middle 1
", to_string(&tree.root));
        check_balances(&tree.root);

        tree.remove(&16);
        assert_eq!("      Middle 31
    Middle 30
      Middle 29
  Left 28
        Middle 27
      Middle 26
        Middle 25
    Right 24
      Middle 23
Middle 15
      Left 14
        Middle 13
    Middle 12
        Middle 11
      Right 10
  Middle 8
        Middle 7
      Middle 6
        Middle 5
    Middle 3
      Left 2
        Middle 1
", to_string(&tree.root));
        check_balances(&tree.root);

        tree.remove(&5);
        assert_eq!("      Middle 31
    Middle 30
      Middle 29
  Left 28
        Middle 27
      Middle 26
        Middle 25
    Right 24
      Middle 23
Middle 15
      Left 14
        Middle 13
    Middle 12
        Middle 11
      Right 10
  Middle 8
        Middle 7
      Right 6
    Middle 3
      Left 2
        Middle 1
", to_string(&tree.root));
        check_balances(&tree.root);

        tree.remove(&6);
        assert_eq!("      Middle 31
    Middle 30
      Middle 29
  Left 28
        Middle 27
      Middle 26
        Middle 25
    Right 24
      Middle 23
Middle 15
      Left 14
        Middle 13
    Middle 12
        Middle 11
      Right 10
  Middle 8
      Middle 7
    Left 3
      Left 2
        Middle 1
", to_string(&tree.root));
        check_balances(&tree.root);

        tree.remove(&7);
        assert_eq!("      Middle 31
    Middle 30
      Middle 29
  Left 28
        Middle 27
      Middle 26
        Middle 25
    Right 24
      Middle 23
Middle 15
      Left 14
        Middle 13
    Middle 12
        Middle 11
      Right 10
  Right 8
      Middle 3
    Middle 2
      Middle 1
", to_string(&tree.root));
        check_balances(&tree.root);

        tree.remove(&1);
        assert_eq!("      Middle 31
    Middle 30
      Middle 29
  Left 28
        Middle 27
      Middle 26
        Middle 25
    Right 24
      Middle 23
Middle 15
      Left 14
        Middle 13
    Middle 12
        Middle 11
      Right 10
  Right 8
      Middle 3
    Right 2
", to_string(&tree.root));
        check_balances(&tree.root);

        tree.remove(&11);
        assert_eq!("      Middle 31
    Middle 30
      Middle 29
  Left 28
        Middle 27
      Middle 26
        Middle 25
    Right 24
      Middle 23
Middle 15
      Left 14
        Middle 13
    Right 12
      Middle 10
  Right 8
      Middle 3
    Right 2
", to_string(&tree.root));
        check_balances(&tree.root);

        tree.remove(&15);
        assert_eq!("      Middle 31
    Middle 30
      Middle 29
  Left 28
        Middle 27
      Middle 26
        Middle 25
    Right 24
      Middle 23
Right 14
      Middle 13
    Middle 12
      Middle 10
  Middle 8
      Middle 3
    Right 2
", to_string(&tree.root));
        check_balances(&tree.root);
    }

    #[test]
    fn test_remove_largest() {
        let mut tree = HeightBalancedTree {
            root:
            build_tree(
                build_tree(None,
                           2,
                           build_node(3),
                           Balance::Right),
                8,
                build_tree(build_node(10),
                           12,
                           build_tree(build_node(13),
                                      14,
                                      None,
                                      Balance::Left),
                           Balance::Right),
                Balance::Right),
        };
        assert_eq!("    Left 14
      Middle 13
  Right 12
    Middle 10
Right 8
    Middle 3
  Right 2
", to_string(&tree.root));
        check_balances(&tree.root);

        assert_eq!(remove_largest(&mut tree.root), 14);
        assert_eq!("    Middle 13
  Middle 12
    Middle 10
Middle 8
    Middle 3
  Right 2
", to_string(&tree.root));
        check_balances(&tree.root);

        assert_eq!(remove_largest(&mut tree.root), 13);
        assert_eq!("  Left 12
    Middle 10
Middle 8
    Middle 3
  Right 2
", to_string(&tree.root));
        check_balances(&tree.root);

        assert_eq!(remove_largest(&mut tree.root), 12);
        assert_eq!("  Middle 10
Left 8
    Middle 3
  Right 2
", to_string(&tree.root));
        check_balances(&tree.root);

        assert_eq!(remove_largest(&mut tree.root), 10);
        assert_eq!("  Middle 8
Middle 3
  Middle 2
", to_string(&tree.root));
        check_balances(&tree.root);

        assert_eq!(remove_largest(&mut tree.root), 8);
        assert_eq!("Left 3
  Middle 2
", to_string(&tree.root));
        check_balances(&tree.root);

        assert_eq!(remove_largest(&mut tree.root), 3);
        assert_eq!("Middle 2
", to_string(&tree.root));
        check_balances(&tree.root);

        assert_eq!(remove_largest(&mut tree.root), 2);
        assert_eq!("", to_string(&tree.root));
        check_balances(&tree.root);
    }

    #[test]
    #[should_panic]
    fn test_remove_largest_panic_on_null_root() {
        remove_largest::<i32>(&mut None);
    }

    #[test]
    fn test_merge() {
        {
            let mut t1 = HeightBalancedTree {
                root:
                build_tree(
                    build_tree(
                        build_node(3),
                        6,
                        build_tree(
                            None,
                            10,
                            build_node(13),
                            Balance::Right),
                        Balance::Right),
                    15,
                    build_tree(
                        build_node(17),
                        23,
                        None,
                        Balance::Left),
                    Balance::Left)
            };
            let t2 = HeightBalancedTree {
                root:
                build_tree(
                    build_tree(
                        build_node(33),
                        36,
                        build_tree(
                            None,
                            40,
                            build_node(43),
                            Balance::Right),
                        Balance::Right),
                    45,
                    build_tree(
                        build_node(47),
                        53,
                        None,
                        Balance::Left),
                    Balance::Left)
            };

            check_balances(&t1.root);
            check_balances(&t2.root);
            assert_eq!("  23
    17
15
      13
    10
  6
    3
", format!("{:?}", t1));
            assert_eq!("  53
    47
45
      43
    40
  36
    33
", format!("{:?}", t2));

            t1.merge(t2);
            assert_eq!("    53
      47
  45
        43
      40
    36
      33
23
      17
    15
      13
  10
    6
      3
", format!("{:?}", t1));
            check_balances(&t1.root);
        }
    }
}
