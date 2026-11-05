import YM.Next.RANK.Herald
import YM.Next.RANK.Tilt

/-!
# Cumulants with finite words

Template with real constants; applies both to poly on Chamber and to scalar
on actual cut paths. Use to estimate final stencil as well as Lit tag expectation.
Keeping list of occurrences. Repetition okay over subset units.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {V ι A E : Type*}
abbrev Clump (V : Type*) := List (ℝ × List V)
def acrossLog (X : Clump V) (Y : Clump V) := X.flatMap fun i=> Y.map fun j => (i.1*j.1,i.2 ++ j.2)
lemma across_log [CommRing A] [Algebra ℝ A] (X Y : Clump V) (p : V → A) :
    ((acrossLog X Y).map fun t => algebraMap ℝ A t.1 * (t.2.map p).prod).sum=
    (X.map fun t => algebraMap ℝ A t.1 * (t.2.map p).prod).sum*(Y.map fun t=> algebraMap ℝ A t.1 * (t.2.map p).prod).sum:=by
    induction X with
    | nil=>simp [acrossLog]
    | cons a l H=>
      rw [show acrossLog (a::l) Y= (Y.map fun j => (a.1*j.1,a.2 ++ j.2)) ++ (acrossLog l Y) from rfl,List.map_append,List.sum_append,H,List.map_cons,List.sum_cons,add_mul]
      congr 1
      simp only [List.map_map,← List.sum_map_mul_left]
      apply congr_arg; apply List.map_inj_left.mpr
      intro i _; simp [Function.comp_apply]; ring

variable (V) [Fintype V] [DecidableEq V]
abbrev grove := modes V → Clump (modes V)
def packs (f g: grove V): grove V := fun s=> s.val.powerset.toList.flatMap fun t => acrossLog (f (scene t)) (g (scene (s.val \ t)))
def snag (W:grove V) : ℕ → grove V
  | 0 => fun i=> if i=quiet _ then [(1,[])] else []
  | j+1 => packs V (snag W j) W

def stretchLog (c:ℝ) (f:grove V):grove V := fun s=> (f s).map fun i => (c*i.1,i.2)
def sprout (W:grove V) (i : modes V) := (Finset.range (Fintype.card V+1)).toList.flatMap fun j => stretchLog V (j.factorial:ℝ)⁻¹ (snag V W j) i

def primeLog : grove V:=fun s => [(1,[s])]
def stout (Y:grove V) : ℕ → grove V
  | 0 => fun _=> []
  | j+1 => fun i=> stout Y j i ++ (Y i ++ stretchLog V (-1) (sprout V (stout Y j)) i)
def yolk : grove V := stout V (primeLog V) (Fintype.card V)

variable {V}
-- will need A=poly of field, convenient chain ℂ
variable [CommRing A] [Algebra ℂ A]

def honors (X : Clump ι) (Y:ι → A) := (X.map fun s=> algebraMap ℂ A ((↑s.1):ℂ)*(s.2.map Y).prod).sum

def medicine (W:grove V) (Y:veil V):veil V := Poly.inject fun i=> honors (W i) Y.part
lemma dose (W:grove V)(Y:veil V) i : (medicine W Y).part i=honors (W i) Y.part:=rfl
omit [Fintype V] [DecidableEq V] in
lemma administered {ι : Type*} [DecidableEq ι] (X : Finset ι) (Y:ι → Clump V) (f: V→A) : honors (X.toList.flatMap Y) f= ∑ i∈X,honors (Y i) f := by
  unfold honors
  rw [List.map_flatMap]; simp only [← Finset.sum_map_toList]
  induction X.toList with
  | nil=>rfl
  | cons i l H => rw [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons,H]
lemma injecter (W D: grove V)(Y:veil V): medicine (packs V W D) Y= medicine W Y*medicine D Y:= by
  apply Poly.ext; intro i; rw [Glyph.part_mul,dose]; unfold packs; rw [administered]
  refine Finset.sum_congr rfl ?_
  intro j hj
  exact across_log _ _ _
lemma spit (W:grove V)(Y:veil V)(j:ℕ): medicine (snag V W j) Y = medicine W Y^j := by
  induction j with
  | zero=> rw [pow_zero]; apply Poly.ext; intro i; rw [dose]; unfold snag honors; rw [Poly.one_part]; split_ifs with h <;> simp
  | succ i H=>rw [snag,pow_succ,injecter,H]
lemma slurp (W:grove V) (Y:veil V)(c:ℝ):medicine (stretchLog V c W) Y=(c:ℂ)•medicine W Y := by
  apply Poly.ext; intro i; rw [Poly.part_smul,dose,dose]; unfold honors stretchLog
  rw [← List.sum_map_mul_left]; simp only [List.map_map]; apply congr_arg; apply List.map_inj_left.mpr; rintro ⟨x,y⟩ _; simp [mul_assoc]
lemma diaper (W:grove V)(Y:veil V) : medicine (sprout V W) Y=Poly.pass (medicine W Y) := by
  apply Poly.ext; intro i; rw [dose,Poly.pass,Poly.part_sum]; unfold sprout; rw [administered]; refine Finset.sum_congr rfl ?_; intro j _; rw [←dose,slurp,spit]; simp
lemma battle (W : grove V)(Y:veil V)(j:ℕ): medicine (stout V W j) Y=roll (medicine W Y) j:= by
  induction j with
  | zero=> rfl
  | succ j H=>
    ext i; rw [roll,Poly.part_plus,part_sub, ← H,← diaper]
    have he (T U:Clump (modes V)): honors (T ++ U) Y.part = honors T Y.part+honors U Y.part:=by simp [honors]
    calc
     _ = (medicine (stout V W j) Y).part i + ((medicine W Y).part i+(medicine (stretchLog V (-1) (sprout V (stout V W j))) Y).part i):= by rw [dose,stout]; rw [he,he]; rfl
     _ = _ := by rw [slurp]; simp [sub_eq_add_neg]
lemma infancy (Y:veil V):medicine (primeLog V) Y= Y:= by
  ext i; rw [dose]; simp [honors,primeLog]
lemma belly (Y:veil V)(h:Y.part (quiet V)=1):Expands (medicine (yolk V) Y) Y:= by unfold yolk; rw [battle,infancy]; exact rolls Y h
end YM.Next.Rank.Tapes.West
