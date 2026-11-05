import YM.Contacts.Coherent
import YM.OPE.Exchange.Regime

/-!
# Finite combinations having a single logarithmic layer cost

For the signed estimates we do **not** lose a fixed power of a smaller
separation in paying for all the labels of a larger geometry. The worst min
gap bound on a full word would do that, even without any subtractions. We
also cannot simply chain the one-scale OPE at each vertex: a ratio can tend
to 0 too slowly, and it can happen that rematching an inner vertex much more
accurately is required by the error demand at the outer vertex.

Instead refine filters so that scales are in (possibly *equal*) log-rate layers.
Test the complete expression in each layer. In this file define the 'regular'
objects within a layer, and multiplicativity. In this part the timing variable
will go to infinity (e.g. log reciprocal minimum gap).
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Layers
open Function Filter Set MeasureTheory Table OPE
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {L : Register G} {S : Table L} {P : DiffPlan S} {I J W : Type} [Fintype I] [Fintype J]
variable {φ : Filter W} {T : W → ℝ} {a b c d s u v : ℝ}
variable {x y : W → E4} {X : W→ I→E4} {Y : W→ J→ E4}
variable {A B A' B' : Set (W → E4)}

lemma rate_linear {E F : Type} [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (U : E →L[ℂ] F) (hT : Tendsto T φ atTop) {f : W → E} (h : RateLE φ T f a) : RateLE φ T (U ∘ f) a := by
  refine ((RateLE.const ‖U‖ hT).bil h (u:=U ∘ f) (Eventually.of_forall fun p=> by simpa only [Function.comp_apply,norm_norm] using U.le_opNorm (f p)) |>.mono (zero_add a |>.le)) -- fix

/-- Cross separations in T units. -/
def Cross (φ : Filter W) (T : W→ℝ) (s : ℝ) (A B : Set (W→ E4)) :=
  ∀ x∈A, ∀ y∈ B, Intervals φ T s (sole ∘ x) (sole ∘ y)

/-- A palette of paths; no mutual gap asked. Only a gap between palettes or inside strict
pieces. Thus two alternatives in a polynomial can be located anywhere in the same palette. -/
def carries (A : Set (W → E4)) (X : W→ I→ E4) := ∀ i, (fun t=> X t i)∈ A

def pack (X : W→ I→ E4) : Set (W→ E4) := Set.range (fun i : I=>fun t=> X t i)
omit [Fintype I] in
lemma pack_carries : carries (pack X) X:= fun _=> Set.mem_range_self _
lemma Cross.into (h : Cross φ T s A B) (hx : A'⊆ A) (hy : B' ⊆ B) : Cross φ T s A' B' :=
  fun x hp y hh=> h x (hx hp) y (hy hh)
lemma Cross.swap (h : Cross φ T s A B) : Cross φ T s B A := fun y hy x hx=> (h x hx y hy).swap
lemma Cross.mono (h : Cross φ T s A B) (he : s ≤ v) : Cross φ T v A B := fun x hx y hy=> (h x hx y hy).mono he
lemma Cross.union (h : Cross φ T s A B) (h' : Cross φ T s A B') : Cross φ T s A (B ∪ B') := fun x hx y hy=> hy.elim (h x hx y) (h' x hx y)
lemma Cross.windows (h : Cross φ T s A B) (hx : carries A X) (hy : carries B Y) : Intervals φ T s X Y := by
  intro a ha; have he (i j) := h _ (hx i) _ (hy j) a ha
  filter_upwards [eventually_all.mpr fun i=> eventually_all.mpr fun j=> he i j] with t ht i j using ht i j () ()
omit [Fintype I] [Fintype J] in
lemma Cross.packet (h : Intervals φ T s X Y) : Cross φ T s (pack X) (pack Y) := by
  rintro f ⟨i,rfl⟩ g ⟨j,rfl⟩ a ha; exact (h a ha).mono fun t h _ _=> h i j
lemma pack_windows : pack (sole ∘ x) = {x} := Set.Subset.antisymm (by rintro f ⟨⟨⟩,rfl⟩; exact Set.mem_singleton _) (singleton_subset_iff.mpr ⟨(),rfl⟩)
lemma Cross.left (h : Cross φ T s A B) (hx : x∈A) (hy : carries B Y) : Intervals φ T s (sole ∘ x) Y := h.windows (fun _=>hx) hy
omit [Fintype I] [Fintype J] in
lemma pack_seams (X : W→ I→ E4) (Y : W→ J→ E4) : pack (fun t=>beside (X t) (Y t))=pack X ∪ pack Y := by
  ext p; change (_∈ range _) ↔ p∈ range _ ∨ p∈ range _; simp [Sum.exists]
lemma weight_seams (x : I→L.Token) (y : J→L.Token) : sigma (beside x y) = sigma x + sigma y := by rw [sigma,Fintype.sum_sum_type]; rfl
lemma weight_sole (x : L.Token) : sigma (sole x)=x.fst := by simp [sole,sigma]

/-- finite sums of expressions whose terms are each affordable absolutely in this single layer
(note: overlaps allowed between terms). Prices in d times log time units. -/
inductive Fine (M : Devices P) (φ : Filter W) (T : W → ℝ) (A : Set (W → E4)) (s c : ℝ) : (W→Expression P)→ Prop
| zero : Fine M φ T A s c 0
| atom (I : Type) [Fintype I] {X : W → I→ E4} {p : I → L.Token} {f : W → ℂ} (hX : Kept φ T s X) (hA : carries A X) (hf : RateLE φ T f (c-(sigma p:ℝ)*s)) : Fine M φ T A s c (fun t=>f t • tokenWord M.basis (X t) p)
| plus {x y : W → Expression P} : Fine M φ T A s c x → Fine M φ T A s c y → Fine M φ T A s c (x+y)
| germ {x y : W → Expression P} : Fine M φ T A s c x → x =ᶠ[φ] y → Fine M φ T A s c y

variable {M : Devices P} {E E' F : W → Expression P} {f : W→ℂ}
namespace Fine
lemma admits (h : Fine M φ T A s c E) (hu : c ≤ d) (hv : A ⊆ A') : Fine M φ T A' s d E := by
  induction h with
  | zero => exact .zero
  | @atom I _ X p f hx hp hf => exact .atom _ hx (fun i=>hv (hp i)) (hf.mono (sub_le_sub_right hu _))
  | plus _ _ hx hy => exact .plus hx hy
  | germ _ h hx => exact .germ hx h
lemma mono (h : Fine M φ T A s c E) (hu : c ≤ d) : Fine M φ T A s d E := h.admits hu (by rfl)
lemma enlarge (h : Fine M φ T A s c E) (hu : A ⊆ A') : Fine M φ T A' s c E := h.admits le_rfl hu
lemma minus (h : Fine M φ T A s c E) : Fine M φ T A s c (-E) := by
  induction h with
  | zero => simpa using (Fine.zero : Fine M φ T A s c _)
  | @atom I _ X p f hx hp hf =>
    apply germ (.atom _ hx hp hf.neg); filter_upwards with t; change -f t • tokenWord _ _ p= _; rw [neg_smul]; rfl
  | plus _ _ hx hy => rw [neg_add]; exact .plus hx hy
  | germ _ h hx => exact .germ hx (h.mono fun _ ht=> congr_arg Neg.neg ht)
lemma diff (hx : Fine M φ T A s c E) (hy : Fine M φ T A s c F) : Fine M φ T A s c (E-F):=by rw [sub_eq_add_neg]; exact hx.plus hy.minus
omit [Fintype I] in
lemma sum {p : Finset I}{E : I → W→ Expression P} (h : ∀ i∈p,Fine M φ T A s c (E i)) : Fine M φ T A s c (∑ i∈p,E i) := by
  induction p using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact .zero
  | insert i p hi ih => rw [Finset.sum_insert hi]; exact (h i (by simp)).plus (ih fun j hj=>h _ (Finset.mem_insert_of_mem hj))
omit [Fintype I] in
lemma sum' {p : Finset I}{E : I → W→ Expression P} (h : ∀ i∈p,Fine M φ T A s c (E i)) : Fine M φ T A s c (fun t=> ∑ i∈p,E i t) := (sum h).germ (Eventually.of_forall fun _=> Finset.sum_apply ..)
lemma times (h : Fine M φ T A s c E) (hh : Fine M φ T B s d F) (hp : Cross φ T s A B) : Fine M φ T (A ∪ B) s (c+d) (E*F):=by
  induction h with
  | zero => rw [zero_mul]; exact .zero
  | @atom I _ X p f hx hA hf =>
    induction hh with
    | zero => rw [mul_zero]; exact .zero
    | @atom J _ Y q g hy hB hg =>
      have he : c-(sigma p:ℝ)*s+(d-(sigma q:ℝ)*s) = c+d - (sigma (beside p q) : ℝ)*s :=by rw [weight_seams,Nat.cast_add]; ring
      refine (.atom _ (p:=beside p q) (hx.chorus hy (hp.windows hA hB)) (fun i=>?_ ) ((hf.mul hg).mono he.le) : Fine M φ T (A ∪ B) s (c+d) _).germ ?_
      · cases i; exacts [Or.inl (hA _),Or.inr (hB _)]
      filter_upwards with t; change (f t*g t) • tokenWord _ _ _=(_ • _)*(_ • _); rw [token_beside, mul_smul,smul_mul_assoc,mul_smul_comm]
    | plus _ _ hx hy => rw [mul_add]; exact hx.plus hy
    | germ _ h hx => exact .germ hx (h.mono fun i he=> congr_arg (f i • tokenWord M.basis (X i) p * ·) he)
  | plus _ _ hx hy => rw [add_mul]; exact hx.plus hy
  | germ _ h hx => exact .germ hx (h.mono fun i he=> congr_arg (· * F i) he)
lemma increase_layer (h : Fine M φ T A s c E) (hs : s ≤ v) : ∃ c' : ℝ, Fine M φ T A v c' E := by
  induction h with
  | zero => exact ⟨0,.zero⟩
  | @atom I _ X p f hx hA hf => exact ⟨c-(sigma p:ℝ)*s+(sigma p:ℝ)*v, .atom _ (hx.mono hs) hA (hf.mono (by linarith only))⟩
  | plus _ _ hx hy => obtain ⟨a,h⟩:=hx; obtain ⟨b,k⟩:=hy; exact ⟨max a b,.plus (h.mono (le_max_left ..)) (k.mono (le_max_right ..))⟩
  | germ _ h hx => exact hx.imp fun _ he => he.germ h
lemma coeff (h : Fine M φ T A s c E) (hf : RateLE φ T f d) : Fine M φ T A s (d+c) (fun i=> f i • E i) := by
  induction h with
  | zero => simp only [Pi.zero_apply,smul_zero]; exact .zero
  | @atom I _ X p g hx hp hg => simpa only [mul_smul] using
      (.atom _ hx hp ((hf.mul hg).mono (le_of_eq (by ring : d+(c-(sigma p:ℝ)*s)=d+c-(sigma p:ℝ)*s))) : Fine M φ T A s (d+c) _)
  | @plus x y _ _ hx hy => exact .germ (hx.plus hy) (Eventually.of_forall fun t=> (smul_add (f t) (x t) (y t)).symm)
  | @germ x y _ h hx => exact .germ hx (h.mono fun i hi=> congr_arg (f i • ·) hi)
lemma oneSite {w : ℕ} (p : L.Ref w) (hf : RateLE φ T f (c-(w:ℝ)*s)) (hx : x∈A) : Fine M φ T A s c (fun i=>f i • insertToken M.basis (x i) ⟨w,p⟩) := by
  have hp := weight_sole (⟨w,p⟩:L.Token)
  refine germ (.atom Unit (p:=sole (⟨w,p⟩:L.Token)) (Kept.sole φ T x s) (fun _=>hx) (by rw [hp]; exact hf)) ?_
  filter_upwards with t; exact congrArg (f t • ·) (token_sole ..)
variable (hT : Tendsto T φ atTop)
include hT
lemma word (p : I → L.Token) (hX : Kept φ T s X) (hA : carries A X) : Fine M φ T A s ((sigma p:ℝ)*s) (fun t=> tokenWord M.basis (X t) p) := by
  have hv : RateLE φ T (fun _=>(1:ℂ)) ((sigma p:ℝ)*s-(sigma p:ℝ)*s):=by rw [sub_self]; exact RateLE.const _ hT
  simpa only [one_smul] using (Fine.atom (M:=M) _ hX hA hv (p:=p))
lemma field {w : ℕ} {p : W → S.Field w} (hx : x∈A) (hp : RateLE φ T p (c-(w:ℝ)*s)) : Fine M φ T A s c (fun i=> insertField M.basis (x i) w (p i)) := by
  let L' := Module.finBasis ℂ (S.Field w)
  apply Fine.germ (sum' (p:=Finset.univ) (E:=fun j i=> L'.repr (p i) j • insertToken M.basis (x i) (⟨w,S.representative w (L' j)⟩:L.Token)) fun i _ => (oneSite (S.representative w (L' i)) (rate_linear (LinearMap.toContinuousLinearMap (L'.coord i)) hT hp) hx))
  filter_upwards with t; dsimp only [insertToken]; simp_rw [S.rep]; conv_rhs=> rw [← (L'.sum_repr (p t)),map_sum]; simp only [map_smul] 
lemma unitOne : Fine M φ T A s 0 1 := by
  let X : W → Empty → E4:= fun _=>0; let v : Empty → L.Token:= fun i=> i.elim; refine Eq.mpr ?_ (word (A:=A) (M:=M) hT v (X:=X) (s:=s) ?_ ?_)
  · simp only [sigma,Fintype.sum_empty,Nat.cast_zero,zero_mul,tokenWord,Fintype.prod_empty]; rfl
  · intro b hb; exact Eventually.of_forall fun _=>OPE.Apart.diagonal _ _
  intro i; exact i.elim
omit [Fintype I] in
lemma product {p : Finset I}{A' : I → Set (W→ E4)}{a : I→ ℝ}{X : I→ W→ Expression P}
    (h : ∀ i∈p,Fine M φ T (A' i) s (a i) (X i)) (he : (p:Set I).Pairwise (fun i j=> Cross φ T s (A' i) (A' j))) : Fine M φ T
      (⋃ i∈p,A' i) s (∑ i∈p,a i) (∏ i∈p,X i) := by
  induction p using Finset.induction_on with
  | empty=> rw [Finset.prod_empty,Finset.sum_empty]; exact unitOne hT
  | @insert i p hi ih=>
    have hu : (p : Set I) ⊆ ↑(insert i p : Finset I) := Finset.coe_subset.mpr (Finset.subset_insert i p)
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.set_biUnion_insert]
    refine times (h i (by simp)) (ih (fun j hj=> h _ (Finset.mem_insert_of_mem hj)) (he.mono hu)) ?_
    intro X hX y hy; obtain ⟨j,hj,hY⟩:= Set.mem_iUnion₂.mp hy; exact he (show i∈ (↑(insert i p : Finset I):Set I) by simp) (hu hj) (fun h=> hi (h ▸ hj)) _ hX _ hY
omit hT
lemma fits {U : W → Set E4} (h : Fine M φ T A s c E) (hA : ∀ x∈ A,∀ᶠ i in φ,x i∈U i) : ∀ᶠ i in φ,E i∈ supportedAt (U i) := by
  induction h with
  | zero => simp only [Pi.zero_apply,zero_mem]; exact Eventually.of_forall fun _=>trivial
  | @atom I _ X p f hx hw hf =>
    filter_upwards [show ∀ᶠ i in φ,∀ j:I, X i j∈U i from eventually_all.mpr (fun j=> hA _ (hw j))] with i hi
    exact (supportedAt (U i)).smul_mem ((supportedAt (U i)).prod_mem (f:= fun j=>insertToken M.basis (X i j) (p j)) (t:=Finset.univ) fun j _=> insert_supportedAt M.basis _ (hi j) _) _
  | plus _ _ hx hy => exact (hx.and hy).mono fun i ⟨hx,hy⟩=> (supportedAt _).add_mem hx hy
  | germ _ h hx => exact (h.and hx).mono fun i ⟨h,hx⟩=> h ▸ hx
end Fine
end YM.Contacts.Layers
