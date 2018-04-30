
import data.list.basic

section left_pad

variables {α : Type*}

open nat

lemma list.cons_repeat (c : α) :
  Π  (n : ℕ), c :: list.repeat c n = list.repeat c n ++ [c] :=
by { intro, symmetry, induction n ; simp *, }

lemma list.take_append (xs ys : list α) (n : ℕ)
  (h : xs.length = n) :
  (xs ++ ys).take n = xs :=
by { subst n, induction xs ; simp! [add_one,*], }

lemma list.drop_append (xs ys : list α) (n : ℕ)
  (h : xs.length = n) :
  (xs ++ ys).drop n = ys :=
by { subst n, induction xs ; simp! [add_one,*], }

def left_pad_aux (c : α) : ℕ → list α → list α
 | 0 xs := xs
 | (succ n) xs := left_pad_aux n (c :: xs)

def left_pad (c : α) (n : ℕ) (x : list α) : list α :=
left_pad_aux c (n - x.length) x

variables (c : α) (n : ℕ) (x : list α)

lemma left_pad_def
: left_pad c n x = list.repeat c (n - x.length) ++ x :=
begin
  simp [left_pad],
  generalize : (n - list.length x) = k,
  induction k generalizing x
  ; simp! [add_one,add_succ,succ_add,list.cons_repeat,*],
end

lemma length_left_pad
: (left_pad c n x).length = max n x.length :=
begin
  simp [left_pad_def],
  cases le_total n x.length with Hk Hk,
  { rw max_eq_right Hk,
    rw ← nat.sub_eq_zero_iff_le at Hk,
    simp *, },
  { simp [max_eq_left Hk],
    rw [← nat.add_sub_assoc Hk,nat.add_sub_cancel_left] },
end

lemma left_pad_prefix
: ∀ c' ∈ (left_pad c n x).take (n - x.length), c' = c :=
by { rw [left_pad_def,list.take_append] ,
     { intro, apply list.eq_of_mem_repeat },
     simp! , }

lemma left_pad_suffix
: (left_pad c n x).drop (n - x.length) = x :=
by simp [left_pad_def,list.drop_append]

end left_pad


section unique

variables {α : Type*} [decidable_eq α]

def unique : list α → list α
 | [] := []
 | (x :: xs) :=
   if x ∈ xs
     then unique xs
     else x :: unique xs

lemma mem_unique (x : α) (xs : list α) :
  x ∈ unique xs ↔ x ∈ xs :=
begin
  induction xs with x' xs ; simp!,
  by_cases x' ∈ xs ; simp *,
  split ; intro h,
  { simp * },
  { cases h ; cc, },
end

lemma nodup_unique (xs : list α) :
  (unique xs).nodup :=
begin
  induction xs with x xs ; simp!,
  by_cases x ∈ xs ; simp [*,mem_unique],
end

end unique

-- These are pretty general lemmas about lists.
-- We could find them in the standard library
namespace list

universes u v w

variables {α : Type u} {β : Type v} {γ : Type w}
variables (f : α → β → γ)
variables {x : α} {y : β} {xs : list α} {ys : list β}

open function

@[simp]
lemma map_eq_nil {f : α → γ} :
  map f xs = nil ↔ xs = nil :=
by cases xs ; simp

@[simp]
lemma zip_eq_nil :
  zip xs ys = nil ↔ xs = nil ∨ ys = nil :=
by cases xs ; cases ys ; simp

lemma map₂_eq_map_zip :
  map₂ f xs ys = map (uncurry f) (zip xs ys) :=
begin
  induction xs generalizing ys,
  { cases ys ; simp, },
  { cases ys ; simp [*,uncurry], }
end

lemma mem_map₂
  (h : (x,y) ∈ zip xs ys) :
  f x y ∈ map₂ f xs ys :=
by { rw map₂_eq_map_zip,
     refine @mem_map_of_mem _ _ (uncurry f) (x,y) _ h, }

@[simp]
lemma cons_tail_tails :
  xs :: tail (tails xs) = tails xs :=
by cases xs ; simp

lemma tails_append {xs' : list α} :
  tails (xs ++ xs') = map (++ xs') (tails xs) ++ (tails xs').tail :=
by induction xs ; simp *

lemma tails_reverse :
  tails (reverse xs) = reverse (map reverse (inits xs)) :=
by induction xs with x xs; simp [tails_append,*,comp]

lemma inits_reverse :
  inits (reverse xs) = reverse (map reverse (tails xs)) :=
by { rw ← reverse_reverse xs,
     generalize : reverse xs = ys,
     simp [tails_reverse,comp],
     symmetry, apply map_id }

@[simp]
lemma sum_reverse [add_comm_monoid α] :
  sum (reverse xs) = sum xs :=
by induction xs ; simp *

end list

section minimum

variables {α : Type*} [decidable_linear_order α] [inhabited α]

def minimum (xs : list α) : α :=
list.foldl min xs.head xs.tail

@[simp]
lemma minimum_single (x : α) :
  minimum [x] = x :=
rfl

open list

@[simp]
lemma minimum_cons (x : α) (xs : list α)
  (h : xs ≠ []) :
  minimum (x :: xs) = min x (minimum xs) :=
by { cases xs with y ys, contradiction,
     simp [minimum], rw ← foldl_hom,
     simp [min_assoc], }

lemma le_minimum {x : α} {xs : list α}
  (h : xs ≠ [])
  (h' : ∀ i, i ∈ xs → x ≤ i) :
  x ≤ minimum xs :=
begin
  induction xs, contradiction,
  by_cases xs_tl = list.nil,
  { subst xs_tl, apply h', simp, },
  simp *, apply le_min,
  { apply h', simp },
  { apply xs_ih h, introv h'',
    apply h', right, apply h'' },
end

@[simp]
lemma minimum_cons_le_self {i : α} {xs : list α} :
  minimum (i :: xs) ≤ i :=
by cases xs ; simp [min_le_left]

lemma minimum_le {i : α} {xs : list α}
  (h : i ∈ xs) :
  minimum xs ≤ i :=
by { induction xs ; cases h,
     { subst i, simp [min_le_left], },
     { have : xs_tl ≠ [],
       { intro, subst xs_tl, cases h },
       simp *, transitivity, apply min_le_right,
       solve_by_elim } }

end minimum

local attribute [instance, priority 0] classical.prop_decidable

-- Here are the specifics of our solution.
-- It hinges on computing lists of partial sums
-- forward (`inits_sums`) and backward (`tails_sums`)
section fulcrum

open list int function

instance : inhabited ℤ :=
⟨ 0 ⟩

def inits_sums.f : list ℤ × ℤ → ℤ → list ℤ × ℤ
 | (xs,acc) x := ((acc+x) :: xs, acc+x)

def partial_sums (xs : list ℤ) : list ℤ :=
(list.foldl inits_sums.f ([0],0) xs).1

def tails_sums (xs : list ℤ) : list ℤ :=
partial_sums xs.reverse

def inits_sums (xs : list ℤ) : list ℤ :=
(partial_sums xs).reverse

def fulcrum (xs : list ℤ) : ℤ :=
let xs' := map₂ (λ i j, abs (i - j)) (inits_sums xs) (tails_sums xs) in
minimum xs'

variables (xs : list ℤ)

@[simp]
def partial_sums_def :
  partial_sums xs.reverse = xs.tails.map sum :=
begin
  simp [partial_sums],
  suffices : foldl inits_sums.f ([0], 0) (reverse xs)
           = (map sum (tails xs), sum xs),            { simpa * },
  induction xs ; simp [*,foldl_reverse,inits_sums.f],
end

@[simp]
def tails_sums_def :
  tails_sums xs = xs.tails.map sum :=
by simp [tails_sums]

@[simp]
def inits_sums_def :
  inits_sums xs = xs.inits.map sum :=
by { rw ← reverse_reverse xs,
     generalize : reverse xs = ys,
     simp [inits_sums,inits_reverse,comp], }

lemma le_fulcrum (x : ℤ)
  (h : ∀ i j, (i,j) ∈ zip (xs.inits.map sum) (xs.tails.map sum) → x ≤ abs (i - j)) :
  x ≤ fulcrum xs :=
begin
  apply le_minimum,
  { simp [map₂_eq_map_zip,decidable.not_or_iff_and_not],
    cases xs ; simp, },
  { simp, introv h', simp [map₂_eq_map_zip,uncurry] at h',
    rcases h' with ⟨ a, b, h₀, h₁ ⟩, subst i,
    apply h _ _ h₀, }
end

lemma fulcrum_le (i j : ℤ)
  (h : (i,j) ∈ zip (xs.inits.map sum) (xs.tails.map sum)) :
  fulcrum xs ≤ abs (i - j) :=
minimum_le $
by { simp, refine mem_map₂ (λ i j, abs (i + -j)) h, }

def fulcrum_idx.f : ℕ × ℤ → ℕ × ℤ → ℕ × ℤ
 | (i,acc) (j,x) :=
if x < acc
  then (j,x)
  else (i,acc)

def fulcrum_idx (xs : list ℤ) : ℕ :=
let xs' := map₂ (λ i j, abs (i - j)) (inits_sums xs) (tails_sums xs) in
(xs'.enum.foldl fulcrum_idx.f (0,0)).1

-- lemma fulcrum_idx_lt_length_self (xs : list ℤ)
--   (h : xs ≠ []) :
--   fulcrum_idx xs < xs.length := sorry

-- local notation `♯`:20 xs := (let h := fulcrum_idx_lt_length_self xs (by assumption) in by cc)

-- lemma fulcrum_idx_spec (i : ℕ)
--   (h₀ : xs ≠ [])
--   (h₁ : i = fulcrum_idx xs) :
--   abs ( (xs.inits.map list.sum).inth i - (xs.tails.map list.sum).inth i ) = fulcrum xs :=
-- begin
--   subst i,
--   simp [fulcrum,-inth,minimum],
-- end

end fulcrum
