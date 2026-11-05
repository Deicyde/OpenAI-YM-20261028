import YM.Euclid.Null

/-!
# Read quotient fields in *the same* Table, or one known to respect its quotient

Representative independence and pointwise ext. Useful for implementing inclusion
and differential identities in all slots without tuple inclusion conversions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Table
open Function Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

variable {G : Gauge} {L : Register G} (S T : Table L)
variable {n : ℕ}

/-- `T.respects S`: e.g., a phase with identities. Does not say it detects
*precisely* these relations. -/
def respects (T S : Table L) : Prop := ∀ d, S.null d ≤ T.null d

theorem agrees (Hp : T.Symmetric) (hr : T.respects S) {x : Points n} (hx : x ∈ conf n)
    {d : Caps n} {v w : L.Vector d} (h : ∀ i, S.project _ (v i) = S.project _ (w i)) :
    T.value d x v = T.value d x w := by
  classical
  let F := T.value d x
  have he (a : Fin n) : v a - w a ∈ T.null (d a) := by
    apply hr
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change S.project _ (v a - w a) = 0
    rw [map_sub, h, sub_self]
  have hz (i : Fin n) (r : L.Vector d) : (F.toLinearMap r i) (v i) = (F.toLinearMap r i) (w i) := by
    rw [← sub_eq_zero,← map_sub]
    let u := update r i (v i-w i)
    change T.value d x u = 0
    rw [← read_eq]
    exact each_place T Hp (he i) hx _ i (by simp [u])
  let A (s : Finset (Fin n)) (i : Fin n) := if i ∈ s then v i else w i
  have hw (s : Finset (Fin n)) : F (A s) = F w := by
    induction s using Finset.induction_on with
    | empty => simp [A]
    | @insert i s hi ih =>
      rw [← ih]
      have hh : A s = update (A s) i (w i) := by
        funext a; by_cases hia : a=i
        · subst a; simp [A,hi]
        simp [update,hia]
      conv_rhs => rw [hh]
      rw [show A (insert i s) = update (A s) i (v i) by
        funext a; by_cases hia : a=i
        · subst a; simp [A]
        simp [A, update, hia]]
      exact hz i (A s)
  rw [← show A Finset.univ=v by simp [A]]; exact hw _

/-- Hierarchy over quotient fields; as always values away from Conf are junk.
If S≠T, require `T.respects S` before *identifying* with T's evaluations. -/
def classMoment (d : Caps n) (x : Points n) : MultilinearMap ℂ (fun i => S.Field (d i)) ℂ :=
  (T.value d x).compLinearMap fun i => S.representative (d i)

theorem class_agrees (hp : T.Symmetric) (hr : T.respects S) (d : Caps n) {x} (hx : x ∈ conf n)
    (v : L.Vector d) :
    S.classMoment T d x (fun i => S.project (d i) (v i)) = T.value d x v :=
  S.agrees T hp hr hx fun _ => S.rep _ _

abbrev Tag := (d : ℕ) × S.Field d
abbrev classTokens (p : L.Token) : S.Tag := ⟨p.1,S.project p.1 p.2⟩

def useAt (x : Points n) (v : Fin n → S.Tag) := S.classMoment T (fun i => (v i).1) x fun i => (v i).2

theorem at_project (hp : T.Symmetric) (hr : T.respects S) {x} (hx : x ∈ conf n) (v : Fin n → L.Token) :
    S.useAt T x (S.classTokens ∘ v) = T.read x v := class_agrees S T hp hr _ hx _

theorem at_unit (H : S.Basic) {x} (hx : x ∈ conf (n+1)) (v : Fin n → S.Tag) (d : ℕ) :
    S.useAt S x (Fin.cons ⟨d,S.unit d⟩ v) = S.useAt S (Points.tail x) v := by
  let w : Fin n → L.Token := fun i => ⟨(v i).1,S.representative _ (v i).2⟩
  let F := Fin.cons (α := fun _ : Fin (n+1) => L.Token) (L.one d) w
  have he (i) : S.classTokens (w i) = v i := by
    change Sigma.mk (v i).1 (S.project _ (S.representative _ _)) = v i
    rw [S.rep]
  rw [show (Fin.cons (α := fun _ => S.Tag) ⟨d,S.unit d⟩ v) = S.classTokens ∘ F by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [F,Function.comp_apply,Fin.cons_zero]; rfl
    · simp only [F,Function.comp_apply, Fin.cons_succ,he], at_project S S H.toSymmetric (fun _ => le_rfl) hx,
    H.unital hx d w]
  rfl

/-- Reply ext lemma using *other quotient fields*, no unit scaling implicit. -/
theorem through (h : S.Symmetric) {d : ℕ} (p : S.Field d) (w : Fin n → L.Token) {x}
    (hx : x ∈ conf (n+1)) : S.useAt S x (Fin.cons ⟨d,p⟩ (S.classTokens ∘ w)) =
      S.spectra d p ⟨n,x,w,hx⟩ := by
  obtain ⟨v,rfl⟩ := S.onto d p
  let U := (Fin.cons (α := fun _ => L.Token) ⟨d,v⟩ w)
  rw [show Fin.cons (α := fun _ => S.Tag) ⟨_,S.project d v⟩ (S.classTokens ∘ w) =
    S.classTokens ∘ U by
    ext1 i; refine Fin.cases ?_ (fun j => ?_) i <;> simp only [U, Function.comp_apply,
      Fin.cons_succ, Fin.cons_zero]]
  exact S.at_project S h (fun _ => le_rfl) hx U

theorem field_ext {d : ℕ} {A B : S.Field d} (hp : S.Symmetric)
    (H : ∀ (n : ℕ) (q : Fin n → S.Tag), ∀ x ∈ conf (n+1),
      S.useAt S x (Fin.cons ⟨d,A⟩ q) = S.useAt S x (Fin.cons ⟨d,B⟩ q)) : A=B := by
  apply S.faithfully
  funext a; rcases a with ⟨m,x,w,hx⟩
  rw [← through S hp A, ← through S hp B, H _ _ x hx]

theorem class_perm (h : T.Symmetric) (p : Equiv.Perm (Fin n)) {x} (hx : x ∈ conf n) (w : Fin n → S.Tag) :
    S.useAt T (Points.rearrange p x) (w ∘ p) = S.useAt T x w := by
  let v : Fin n → L.Token := fun i => ⟨(w i).1,S.representative (w i).1 (w i).2⟩
  exact h.same p hx v

theorem class_smooth (h : T.Smooth) (w : Fin n → S.Tag) :
    ContDiffOn ℝ ∞ (fun x => S.useAt T x w) (conf n) := by
  let v : Fin n → L.Token := fun i => ⟨(w i).1,S.representative (w i).1 (w i).2⟩
  exact T.smooth_read h v
end YM.Table
