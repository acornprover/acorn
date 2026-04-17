# Attributes

## Prove With Match Statement

An example found when migrating pre-match code.

```acorn
    type Nat: axiom
    attributes Nat {
        define suc(self) -> Nat { axiom }
    }

    inductive Int {
        from_nat(Nat)
        neg_suc(Nat)
    }

    define abs_case_1(a: Int, n: Nat) -> Bool {
        a = Int.from_nat(n)
    }

    define abs_case_2(a: Int, n: Nat) -> Bool {
        exists(k: Nat) {
            a = Int.neg_suc(k) and n = k.suc
        }
    }

    define abs(a: Int) -> Nat {
        match a {
            Int.from_nat(n) {
                n
            }
            Int.neg_suc(k) {
                k.suc
            }
        }
    }

    theorem goal(a: Int) {
        abs_case_1(a, abs(a)) or abs_case_2(a, abs(a))
    } by {
        match a {
            Int.from_nat(n) {
                abs_case_1(a, abs(a))
            }
            Int.neg_suc(k) {
                abs_case_2(a, abs(a))
            }
        }
    }
    
```

## Proving With Generic Structure

Just testing that we can define something, then immediately prove the definition.

```acorn
    structure Pair[T, U] {
        first: T
        second: U
    }

    attributes Pair[T, U] {
        define swap(self) -> Pair[U, T] {
            Pair.new(self.second, self.first)
        }
    }

    theorem swap_def[T, U](p: Pair[T, U]) {
        p.swap = Pair.new(p.second, p.first)
    }
    
```

## Normalizing Instance Aliases

```acorn
    typeclass M: Magma {
        mul: (M, M) -> M
    }

    inductive Foo {
        foo
    }

    attributes Foo {
        define mul(self, other: Foo) -> Foo {
            Foo.foo
        }
    }

    instance Foo: Magma {
        let mul: (Foo, Foo) -> Foo = Foo.mul
    }

    theorem goal(a: Foo) {
        Magma.mul(a, a) = a * a
    }
    
```

## Proving With Generic Let Attribute

```acorn
    structure Box[T] {
        item: T
    }

    attributes Box[T] {
        let const_false: T -> Bool = function(x: T) {
            false
        }
    }

    theorem goal {
        true
    }
    
```

## Proving With Let Satisfy Attribute

```acorn
    inductive One {
        one
    }
    attributes One {
        let witness: One satisfy {
            witness = One.one
        }
    }
    theorem goal {
        One.witness = One.one
    }
    
```

## Proving With Function Satisfy Attribute

```acorn
    inductive One {
        one
    }
    attributes One {
        let identity(a: Bool) -> b: Bool satisfy {
            b = a
        }
    }
    theorem goal(a: Bool) {
        One.identity(a) = a
    }
    
```

## Typeclass Attribute Semantics

```acorn
    typeclass A: Addable {
        zero: A
        add: (A, A) -> A
    }

    attributes A: Addable {
        define plus_zero(self) -> A {
            A.add(self, A.zero)
        }
    }

    theorem goal[A: Addable](x: A) {
        x.plus_zero = A.add(x, A.zero)
    }
    
```

## Redefining Provided Attribute Works

```acorn
    typeclass A: Arf {
        vacuous_condition {
            true
        }
    }

    attributes A: Arf {
        define flag(self) -> Bool {
            false
        }
    }

    inductive Foo {
        foo
    }

    instance Foo: Arf

    attributes Foo {
        define flag(self) -> Bool {
            true
        }
    }

    theorem goal(f: Foo) {
        f.flag
    }
    
```

## Proving With Attribute Params

```acorn
    structure BoolPair {
        first: Bool
        second: Bool
    }

    attributes BoolPair {
        define apply_first<T>(self, f: Bool -> T) -> T {
            f(self.first)
        }
    }

    theorem type_attr_syntax(b: BoolPair, f: Bool -> Bool) {
        BoolPair.apply_first(b, f) = f(b.first)
    }

    theorem obj_attr_syntax(b: BoolPair, f: Bool -> Bool) {
        b.apply_first(f) = f(b.first)
    }

    structure Pair<T, U> {
        first: T
        second: U
    }

    attributes Pair<T, U> {
        define map_first<V>(self, f: T -> V) -> V {
            f(self.first)
        }
    }

    theorem type_attr_generic<A, B, C>(p: Pair<A, B>, f: A -> C) {
        Pair.map_first(p, f) = f(p.first)
    }

    theorem obj_attr_generic<A, B, C>(p: Pair<A, B>, f: A -> C) {
        p.map_first(f) = f(p.first)
    }
    
```

## Proving With Generic Attribute Match

```acorn
    inductive Option<T> {
        none
        some(T)
    }

    attributes Option<T> {
        define map<U>(self, f: T -> U) -> Option<U> {
            match self {
                Option.none {
                    Option.none<U>
                }
                Option.some(t) {
                    Option.some(f(t))
                }
            }
        }
    }

    theorem goal<T, U>(t: T, f: T -> U) {
        Option.some(t).map(f) = Option.some(f(t))
    }
    
```

## Proving With Typeclass Constrained Attributes

Test that we can define attributes with typeclass constraints (Foo[T: Bar] syntax)
and prove a simple theorem using them

```acorn
    inductive Color {
        red
        blue
    }

    structure Set[K] {
        contains: K -> Bool
    }

    typeclass T: HasCompare {
        compare: (T, T) -> Bool
    }

    let color_compare: (Color, Color) -> Bool = axiom

    instance Color: HasCompare {
        let compare: (Color, Color) -> Bool = color_compare
    }

    // Define an attribute on Set[T: HasCompare]
    attributes Set[T: HasCompare] {
        define has_both(self, a: T, b: T) -> Bool {
            self.contains(a) and self.contains(b)
        }
    }

    theorem has_both_def(s: Set[Color], a: Color, b: Color) {
        s.has_both(a, b) = (s.contains(a) and s.contains(b))
    }
    
```

## Proving With Complex Attributes

Test that we can define attributes with typeclass constraints (Foo[T: Bar] syntax)
and prove a simple theorem using them

```acorn
    inductive Color {
        red
        blue
    }

    structure Set[K] {
        contains: K -> Bool
    }

    attributes Set[Color] {
        define has_red(self) -> Bool {
            exists(a: Color) {
                self.contains(Color.red)
            }
        }

        define has_non(self, c: Color) -> Bool {
            exists(a: Color) {
                self.contains(a) and a != c
            }
        }

        define red_splits(self) -> Bool {
            self.has_red and self.has_non(Color.red)
        }
    }

    define true_fn(c: Color) -> Bool {
        true
    }

    let universal = Set.new(true_fn)

    theorem goal {
        universal.red_splits
    } by {
        let b = Color.blue
        universal.contains(b) and b != Color.red
        universal.has_non(Color.red)
        universal.contains(Color.red)
        universal.has_red
    }
    
```
