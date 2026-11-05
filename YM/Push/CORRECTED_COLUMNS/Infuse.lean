import Mathlib.RingTheory.Nilpotent.Exp
import YM.Bid.Craft
import YM.Org.Theatre
import YM.Push.CORRECTED_COLUMNS.Program

/-!
# Insert the correction at an intermediate endpoint

Original comparison polynomials use actual Wilson labels, WITHOUT the
correction. On the complete all-copy array in the same Markov lens insert
the whole correction, commuting with push. Establish signs, placement and
that even masked-out configurations are subject to the correction; later
local estimates on W−C alone wouldn't suffice to pay it.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected
open Function Set Filter Lattice Wilson MeasureTheory RG Marker Overlay Cells
open scoped Topology BigOperators Matrix.Norms.Frobenius

section Algebra
namespace Marks
variable {V : Type*} [Fintype V] [DecidableEq V]
local instance : Module ℚ (Algebra V) := Module.compHom (Algebra V) (algebraMap ℚ ℂ)
private lemma pass_eq (X : Algebra V) (h : part X ∅=0) : Poly.pass X=IsNilpotent.exp X := by
  have hp := Poly.stops X h _ (Nat.lt_succ_self _)
  rw [Poly.pass,IsNilpotent.exp_eq_sum hp]; apply Finset.sum_congr rfl
  intro i _
  change _=(algebraMap ℚ ℂ ((i.factorial:ℚ)⁻¹)) • (X^i)
  rw [map_inv₀,map_natCast]
lemma absorb (X Y : Algebra V) (h : part X ∅=0) (hv : part Y ∅=0) : Poly.pass (X+Y)=Poly.pass X*Poly.pass Y := by
  have he {X : Algebra V} (h : part X ∅=0) : IsNilpotent X := ⟨_,Poly.stops X h _ (Nat.lt_succ_self _)⟩
  rw [pass_eq (X+Y) (by change part X ∅+part Y ∅=0; rw [h,hv,add_zero]),pass_eq X h,pass_eq Y hv]
  exact IsNilpotent.exp_add_of_commute (Commute.all ..) (he h) (he hv)
lemma pass_zero : Poly.pass (0 : Algebra V)=1 := (pass_eq _ rfl).trans IsNilpotent.exp_zero
lemma absorbMany {α} (s : Finset α) (X : α → Algebra V) (h : ∀ i, part (X i) ∅=0) :
    Poly.pass (∑ i∈s,X i) = ∏ i∈s, Poly.pass (X i) := by
  classical
  have he (p : Finset α) : part (∑ i∈p,X i) ∅=0 := by unfold part; rw [Poly.part_sum]; exact Finset.sum_eq_zero fun i _ => h i
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty,pass_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi,Finset.prod_insert hi, absorb _ _ (h i) (he _), ih]

variable {I : Type*} [DecidableEq I] [Fintype I]
def injectSubset (i : I) (s : Finset V) := s.image fun v => (i,v)
omit [Fintype I] in
lemma listed {i : I} {s : Finset (I × V)} (h : located s {i}) : s=injectSubset i (fibre s i) := by
  ext ⟨j,v⟩; simp only [injectSubset,Finset.mem_image,fibre,Finset.mem_filter,Prod.mk.injEq,Finset.mem_univ,true_and]
  constructor
  · intro he; have ht : j=i := Finset.mem_singleton.mp (h _ he)
    exact ⟨v, ht ▸ he,ht.symm,rfl⟩
  rintro ⟨v,h,rfl,rfl⟩; exact h
omit [Fintype I] in
lemma tracks (i : I) (s : Finset V) : located (injectSubset i s) {i} ∧ fibre (injectSubset i s) i=s := by
  constructor
  · intro j hj; obtain ⟨v, hv,h⟩ := Finset.mem_image.mp hj; subst j; simp
  ext j; simp [injectSubset,fibre]

lemma into_send (X : Algebra V) (i : I) :
    into X i=∑ z : (all V).Mode, Poly.send (Marks.mode (injectSubset i z.val)) (X.part z) := by
  ext z
  rcases z with ⟨z,hz⟩
  change Marks.part _ z= Marks.part _ z
  rw [belongs]; unfold part; rw [Poly.part_sum]; split_ifs with h
  · rw [Finset.sum_eq_single (mode (fibre z i))]
    · simp only [Poly.part_send, mode_inj, if_pos (listed h)]
    · intro b _ hb
      have hh : z ≠ injectSubset i b.val := by intro a; refine hb (Subtype.ext ?_); simp only [a,(tracks ..).2]
      rw [Poly.part_send,if_neg fun H => hh (mode_inj.mp H)]
    simp
  symm; apply Finset.sum_eq_zero
  intro k _
  have ht : z≠injectSubset i k.val := fun w => h (w.symm ▸ (tracks i k.val).1)
  simp only [Poly.part_send, mode_inj, if_neg ht]
lemma into_atom (s : Finset V) (c : ℂ) (i : I) :
    into (Poly.send (mode s) c) i=Poly.send (mode (injectSubset i s)) c := by
  rw [into_send, Finset.sum_eq_single (mode s)]
  · simp
  · intro b _ hb; simp [hb]
  simp

private lemma spread_mul (X Y : Algebra V) (i : I) : into (X*Y) i=into X i*into Y i := by
  ext w
  rcases w with ⟨p,hp⟩
  change part _ p=part _ p
  rw [convolution,belongs]
  by_cases h : located p {i}
  · rw [if_pos h, convolution]
    have ht (s : Finset (I × V)) (hh : s ⊆ p) : located s {i} := fun k hk => h k (hh hk)
    have he : p.powerset = (fibre p i).powerset.image (injectSubset i) := by
      ext s; constructor
      · intro a; have hm := Finset.mem_powerset.mp a
        apply Finset.mem_image.mpr; refine ⟨fibre s i, Finset.mem_powerset.mpr ?_,(listed (ht _ hm)).symm⟩
        intro v hv; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm (Finset.mem_filter.mp hv).2⟩
      intro a; obtain ⟨v,hv,e⟩ := Finset.mem_image.mp a
      subst s; apply Finset.mem_powerset.mpr
      intro u hh; obtain ⟨l,hl,w⟩ := Finset.mem_image.mp hh; exact w ▸ (Finset.mem_filter.mp (Finset.mem_powerset.mp hv hl)).2
    rw [he,Finset.sum_image]; swap
    · intro v hv w hw e; exact (tracks i v).2.symm.trans (e ▸ (tracks i w).2)
    apply Finset.sum_congr rfl
    intro s hs
    have hv : located (p\injectSubset i s) {i} := ht _ Finset.sdiff_subset
    rw [belongs,belongs,if_pos (tracks ..).1,if_pos hv,(tracks ..).2]
    rw [show fibre p i\s=fibre (p\injectSubset i s) i by ext k; simp [fibre,injectSubset]]
  rw [if_neg h]; symm; apply Finset.sum_eq_zero
  intro v hv; rw [belongs,belongs]; split_ifs with H H' H'
  · apply (h ?_).elim
    intro w hw; by_cases h : w∈v
    · exact H _ h
    exact H' w (Finset.mem_sdiff.mpr ⟨hw,h⟩)
  all_goals simp

def emb (i : I) : Marks.Algebra V →ₐ[ℂ] Marks.Algebra (I×V) where
  toFun x := into x i
  map_add' x y := by
    ext ⟨v,hv⟩; change part (into _ _) v=part (into _ _) v+ part (into _ _) v; simp_rw [belongs]; split <;> simp [part]
  map_mul' x y := spread_mul x y i
  map_zero' := by rw [into_send]; simp
  map_one' := by change into (Poly.send (mode ∅) 1) i= _; rw [into_atom]; simp [injectSubset]; rfl
  commutes' x := by change into (Poly.send (mode ∅) x) i= _; rw [into_atom]; simp [injectSubset]; rfl

lemma into_empty (X : Algebra V) (i : I) : part (into X i) ∅=part X ∅ := by rw [belongs]; simp [fibre,located]
lemma pass_into (X : Algebra V) (i : I) (h : part X ∅=0) : into (Poly.pass X) i=Poly.pass (into X i) := by
  rw [pass_eq (into X i) (by rw [into_empty,h]),pass_eq X h]
  exact IsNilpotent.map_exp ⟨_,Poly.stops X h _ (Nat.lt_succ_self _)⟩ (emb (V:=V) i).toRingHom

-- Useful accounting: embedded toll for any actual radius.
lemma into_price (X : Algebra V) (i : I) (w : ℝ) (h : 0<w) :
    Poly.price (fun _ => w) (into X i)≤Poly.price (fun _ => w) X := by
  rw [into_send]
  refine (Poly.batch (fun _ => h) _ _).trans_eq ?_
  unfold Poly.price
  apply Finset.sum_congr rfl
  intro b _
  change Poly.price (fun _ => w) (Poly.send (mode (injectSubset i b.val)) (X.part b))= _
  have hx : Function.Injective (fun j : V => (i,j)) := fun a b h => congr_arg Prod.snd h
  simp only [Poly.solo, Poly.toll,Marks.mode,injectSubset,Finset.prod_const,Finset.card_image_of_injective _ hx]

/-- Exact hand operation on scalar polys. -/
def partner : Algebra V →+* Algebra V where
  toFun X := Poly.inject fun v => star (X.part v)
  map_one' := by ext s; change star ((1 : Algebra V).part s)=_; simp only [Poly.one_part]; split <;> simp
  map_add' := fun x y => by ext s; exact star_add _ _
  map_zero' := by ext s; exact star_zero _
  map_mul' x y := by
    ext s; change star ((x*y).part s)=(Poly.inject _ * Poly.inject _).part _
    rw [Poly.part_mul,Poly.part_mul,star_sum]; apply Finset.sum_congr rfl
    intro i _; rw [star_sum]; apply Finset.sum_congr rfl
    intro k _; split <;> first | exact star_zero _ | exact star_mul' _ _
lemma turns (X : Algebra V) (h : part X ∅=0) : partner (Poly.pass X) = Poly.pass (partner X) := by
  rw [pass_eq X h, pass_eq _ (show star (part X ∅)=0 from by rw [h,star_zero])]
  exact IsNilpotent.map_exp ⟨_,Poly.stops X h _ (Nat.lt_succ_self _)⟩ _


section Mirror
variable {n : Side} {G : Gauge}
open scoped Classical in
def atHand (T : Tiling n) (i : T.Cell) (X : Algebra V) := if T.hand i then partner X else X

lemma mirror_mul (X Y : Config G n → Algebra V) (T : Tiling n) (U) :
    replicate T (fun U => X U*Y U) U=replicate T X U*replicate T Y U := by
  classical
  let P (W : Config G n → Algebra V) (i : T.Cell) := into (atHand T i (W (pull (T.omega i) (T.translateBy i) U))) i
  have ht W : replicate T W U=∏ i,P W i := by
    apply Finset.prod_congr rfl; intro i _
    apply congr_arg (fun x : Algebra V => into x i)
    ext s; change T.copy i (fun X => Poly.part (W X) s) U=Poly.part (atHand T i _) s
    unfold Tiling.copy atHand; by_cases h : T.hand i <;> simp only [h,↓reduceIte]; rfl
  simp_rw [ht,← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl
  intro i _
  change into (atHand T i (X _*Y _)) _= _
  have hh a b : atHand (V:=V) T i (a*b)=atHand T i a*atHand T i b := by unfold atHand; split <;> simp
  rw [hh]
  exact spread_mul ..

lemma mirrors_const (L : Algebra V) (T : Tiling n) (U : Config G n) : replicate T (fun _ => L) U = ∏ i, into (atHand T i L) i := by
  classical
  apply Finset.prod_congr rfl; intro i _; congr 1
  ext s; change T.copy i (fun _ => Poly.part L s) U=Poly.part (atHand T i _) s
  unfold Tiling.copy atHand; by_cases h : T.hand i <;> simp only [h,↓reduceIte]; rfl
lemma at_zero (X : Algebra V) (T : Tiling n) (i) (h : part X ∅=0) : part (atHand T i X) ∅=0 := by
  classical
  unfold atHand; split
  · change star (part X ∅)=0; rw [h,star_zero]
  exact h
lemma sign (X : Algebra V) (T : Tiling n) (i) (h : part X ∅=0) :
    into (atHand T i (Poly.pass (-X))) i=Poly.pass (-into (atHand T i X) i) := by
  classical
  have ht : atHand T i (Poly.pass (-X))=Poly.pass (-atHand T i X) := by
    unfold atHand; split
    · rw [turns (-X) (show -part X ∅=0 by rw [h,neg_zero]), map_neg]
    rfl
  rw [ht,pass_into]
  · rw [show into (-atHand T i X) i= -into (atHand T i X) i from map_neg (emb i) _]
  change -part (atHand T i X) ∅=0; rw [at_zero X T i h,neg_zero]

end Mirror
end Marks
end Algebra

namespace Wire
variable {G : Gauge} {C : Family G} {r m N p : ℕ}
variable {V : Type*} [Fintype V] [DecidableEq V] (B : Wire C r m N p) {k : ℕ}

section
local instance : NormedAddCommGroup (Marks.Algebra V) := inferInstance
-- push Poly as real-linear. Comp ℝ ℂ possible, instance collisions. restrict via PiLp by Poly.def
local instance : NormedSpace ℝ (Marks.Algebra V) := inferInstanceAs (NormedSpace ℝ ((Marks.all V).Mode → ℂ))

private lemma inject_push (F : Config G (C.side N p) → Marks.Algebra V) (h : Integrable F (prior G _)) (hk : k ≤ N) (U) :
    B.push F k hk U=Poly.inject fun i => B.push (fun X => (F X).part i) k hk U := by
  ext x
  let L : Marks.Algebra V →L[ℝ] ℂ := {
    toFun v := v.part x
    map_add' := fun a b => rfl
    map_smul' := fun a b => rfl
    cont := Poly.part_cont _ }
  exact (B.linear_image L F h k hk U).symm
private lemma insert_push (L : Marks.Algebra V) (F : Config G (C.side N p) → Marks.Algebra V)
    (h : Continuous F) (hk : k ≤ N) (U) :
    Poly.inject (R:=Marks.all V) (fun i => B.push (fun X => (L*F X).part i) k hk U)=
      L * Poly.inject fun i => B.push (fun X => (F X).part i) k hk U := by
  rw [← inject_push B F (h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    ← inject_push B (fun X => L*F X) ((continuous_const.mul h).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  let M := LinearMap.toContinuousLinearMap (Algebra.lmul ℂ _ L)
  haveI : IsScalarTower ℝ ℂ (Marks.Algebra V) := inferInstanceAs (IsScalarTower ℝ ℂ ((Marks.all V).Mode → ℂ))
  exact B.linear_image (M.restrictScalars ℝ) _ (h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) _ _ _
end

-- Through any intermediate level in the wire (not just terminal).
def station (hr : r ≤ N) (hk : k ≤ N) (P : Config G (C.side N p) → Marks.Algebra V) (U : Config G (C.side k p)) :
    Marks.Algebra (Site (C.side r p) × V) := Poly.inject fun i =>
      B.push (fun Z => (bare (C.beta N p) Z:ℂ)*Poly.part (Marks.replicate (center C.S p hr 0) P Z) i) k hk U

lemma station_one (L : Marks.Algebra V) (P : Config G (C.side N p) → Marks.Algebra V)
    (h : ∀ i, Continuous fun U => (P U).part i) (hr : r ≤ N) (hk : k ≤ N) (U) :
    let T := center C.S p hr 0
    B.station hr hk (fun X => L*P X) U=(∏ i : T.Cell, Marks.into (Marks.atHand T i L) (show Site (C.side r p) from i)) * B.station hr hk P U := by
  intro T
  let F (Z : Config G (C.side N p)) := (bare (C.beta N p) Z : ℂ) • Marks.replicate T P Z
  have hF : Continuous F := by
    refine (Complex.continuous_ofReal.comp (bare_cont _)).smul ?_
    change Continuous (fun Z => (Marks.replicate T P Z).part)
    apply continuous_pi
    intro x; exact Marks.continuous_array T P (fun i => h _) x.val
  let G := ∏ i : T.Cell,Marks.into (Marks.atHand T i L) i
  have hz Z : Marks.replicate T (fun X => L * P X) Z=G*Marks.replicate T P Z := by
    rw [show Marks.replicate T _ Z= _ from Marks.mirror_mul (fun _=>L) P T Z,Marks.mirrors_const]
  have he := insert_push B G F hF hk U
  change Poly.inject (R:=Marks.all (T.Cell × V)) (fun i => B.push (fun Z => (bare (C.beta N p) Z:ℂ) *
    Poly.part (Marks.replicate T (fun X => L*P X) Z) i) k hk U) = G*_
  rw [← show Poly.inject (fun i => B.push (fun X => (F X).part i) k hk U) = _ from
    (show Poly.inject (R:=Marks.all (T.Cell × V)) (fun i => B.push (fun X => (F X).part i) k hk U) = B.station hr hk P U from rfl), ← he]
  unfold F; simp_rw [Algebra.mul_smul_comm, Poly.part_smul, hz]

lemma station_point (hr : r≤N) (P : Config G (C.side N p) → Marks.Algebra V) (i : Finset (Site (C.side r p) × V)) (U) :
    Marks.part (B.station hr hr P U) i=B.term hr P i U := rfl
end Wire
end YM.Push.Corrected
