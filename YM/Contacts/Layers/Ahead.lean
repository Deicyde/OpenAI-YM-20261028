import YM.Contacts.Layers.Strict

/-! # Multiplicative extension past a layer of scales

Layer closeness is tested against *all* spectators of arbitrary finite exponent cost, uniform through every phase. At a fixed log-rate layer allow even positions just outside all remaining paths in the palette at the same separation layer. Inside the spectator words we may be at distances which cost still higher T-rate (here set the terminal cost rate at one). See `Precision`.

Then to transfer a product, it's enough to have arbitrarily good approximants for each factor. Their costs *at their outgoing scales* are controlled; the geometries might sharpen and thus cause much worse costs when regarded at other scales of a reader. Consequently we order the replacement choices and if necessary choose later ones with much higher precision.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Layers
open Function Filter Set MeasureTheory Table Spec OPE
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {C : Family G} {S : Table C.book} {I J W : Type} [Fintype I] [Fintype J]
variable {F : Extraction.Order} (Z : Final C F S) (M : Devices Z.sector.derivatives)
variable {φ : Filter W} {T : W → ℝ} {c d r s u v : ℝ}
variable {x : W → E4} {A B A' B' : Set (W → E4)}
variable {X : W→ I→E4} {Y : W→ J→ E4}
local notation "D" => M.basis
local notation "EP" => W → Expression Z.sector.derivatives
local notation "TK" => C.book.Token
local notation "Φ" => W → Viewers Z
variable {e f e' : W → Expression Z.sector.derivatives}

/-- Norm bound for every path through the readers; unselected plus all characters. -/
def View (φ : Filter W) (T : W→ℝ) (c : ℝ) (e : EP) : Prop :=
  ∀ s : Φ, RateLE φ T (fun i=>readExpr M.basis (spectator Z (s i)) (e i)) c

namespace View
variable {Z M}
lemma zero : View Z M φ T c 0 := fun _ => by simpa only [Pi.zero_apply, map_zero] using RateLE.zero _ _ c
lemma plus (h : View Z M φ T c e) (k : View Z M φ T c f) (hT : Tendsto T φ atTop) : View Z M φ T c (e+f) := fun s=> by
  simp only [Pi.add_apply,map_add]; exact (h s).add (k s) hT
lemma minus (h : View Z M φ T c e) : View Z M φ T c (-e) := fun s=> by simp only [Pi.neg_apply,map_neg]; exact (h s).neg
lemma coeff (h : View Z M φ T c e) {g : W→ℂ} (hf : RateLE φ T g d) : View Z M φ T (d+c) (fun i=>g i • e i) :=
  fun s=> by simp_rw [map_smul]; exact hf.smul (h s)
lemma mono (h : View Z M φ T c e) (hu : c ≤ d) : View Z M φ T d e:= fun _=>(h _).mono hu
lemma ident (h : View Z M φ T c e) (hx : e =ᶠ[φ] f) : View Z M φ T c f := fun s=> (h s).congr ((hx.mono fun _ hi=> congrArg _ hi) : _ =ᶠ[φ] _ )
lemma link_l {g : W→ℂ} (h : View Z M φ T c (e*f)) (hf : RateLE φ T g d) :
    View Z M φ T (d+c) ((fun i=>g i • e i)*f) := by
  apply View.ident (h.coeff hf); exact Eventually.of_forall fun _=>(smul_mul_assoc ..).symm
lemma link_r {g : W→ℂ} (h : View Z M φ T c (e*f)) (hf : RateLE φ T g d) :
    View Z M φ T (d+c) (e*(fun i=>g i • f i)):= by rw [mul_comm e] at *; exact link_l h hf
lemma tie (h : View Z M φ T c (e*f)) (h' : e =ᶠ[φ] e') : View Z M φ T c (e'*f):= View.ident h (h'.mul (Eventually.of_forall fun _=> rfl))
end View
variable {Z M}

/-- Tests at power cost v in the exterior and s from the palette. Precision below uses v uniformly at rate one. -/
def Against (Z : Final C F S) (M : Devices Z.sector.derivatives) (φ : Filter W) (T : W→ℝ) (A : Set (W → E4)) (s v c : ℝ) (e : W→ Expression Z.sector.derivatives) :=
  ∀ ⦃A' : Set (W → E4)⦄, Cross φ T s A A' → ∀ ⦃q : ℝ⦄ ⦃f⦄, Fine M φ T A' v q f → View Z M φ T (c+q) (e*f)
abbrev Precision (Z : Final C F S) (M : Devices Z.sector.derivatives) (φ : Filter W) (T : W→ℝ) (A : Set (W → E4)) (s c : ℝ) := Against Z M φ T A s 1 c
namespace Against
lemma zero : Against Z M φ T A s v c 0:= by intro B h q f hh; rw [zero_mul]; exact View.zero
lemma mono (h : Against Z M φ T A s v c e) (hu : u ≤ s) (hr : c ≤ d) (he : A ⊆ A') : Against Z M φ T A' u v d e:=
  fun _ hp _ _ hh=> View.mono (h ((hp.into he (by rfl)).mono hu) hh) (add_le_add_left hr _)
lemma plus (h : Against Z M φ T A s v c e) (hh : Against Z M φ T A s v c f) (hT : Tendsto T φ atTop) : Against Z M φ T A s v c (e+f):= by
  intro B hp q g hg; rw [add_mul]; exact View.plus (h hp hg) (hh hp hg) hT
lemma minus (h : Against Z M φ T A s v c e) : Against Z M φ T A s v c (-e):= by intro B hp q g hg; rw [neg_mul]; exact View.minus (h hp hg)
lemma diff (h : Against Z M φ T A s v c e)(h' : Against Z M φ T A s v c f)(hT : Tendsto T φ atTop) : Against Z M φ T A s v c (e-f):=by rw [sub_eq_add_neg]; exact plus h h'.minus hT -- namespace resolution
lemma coeff (h : Against Z M φ T A s v c e) {g : W→ℂ} (hg : RateLE φ T g d) : Against Z M φ T A s v (d+c) (fun i=> g i • e i) := by
  intro B hp q f hh; rw [add_assoc]; exact View.link_l (h hp hh) hg
lemma ident (h : Against Z M φ T A s v c e) (hx : e =ᶠ[φ] f) : Against Z M φ T A s v c f := fun _ hp _ _ hh=> View.tie (h hp hh) hx
lemma times (h : Against Z M φ T A s v c e) (he : Fine M φ T B v d f) (hf : Cross φ T s A B) (hu : s≤v) : Against Z M φ T (A ∪ B) s v (c+d) (e*f) := by
  intro A' hx q g hg; rw [mul_assoc, add_assoc]; exact h (hf.union (hx.into (Set.subset_union_left ..) (by rfl))) (he.times hg ((hx.into (Set.subset_union_right ..) (by rfl)).mono hu))
variable (hT : Tendsto T φ atTop)
include hT
lemma of_words (h : ∀ (I : Type) [Fintype I] (x : W → I→ E4) (p : I→ TK), Kept φ T v x → Cross φ T s A (pack x) → View Z M φ T (c+(sigma p:ℝ)*v) (e*(fun i=> tokenWord M.basis (x i) p))) : Against Z M φ T A s v c e := by
  intro B hp q f hh; induction hh with
  | zero=> rw [mul_zero]; exact View.zero
  | @atom I _ X p f hx hw hf =>
    apply View.mono (View.link_r (h I X p hx ?_) hf) (by linarith only)
    exact hp.into (by rfl) (fun i hi=> by obtain ⟨j,rfl⟩:= hi; exact hw j)
  | plus _ _ hx hy=> rw [mul_add]; exact hx.plus hy hT
  | germ _ h hx => rw [mul_comm e] at *; exact hx.tie h -- at hT?
end Against
lemma Fine.tests [φ.NeBot] (hT : Tendsto T φ atTop) (H : Services C F S) (h : Fine M φ T A s c e) (hs : 0 ≤ s) (hv : s ≤ v) : Against Z M φ T A s v c e := by
  induction h with
  | zero=> exact Against.zero
  | @atom I _ X p f hx ha hf=>
    apply Against.mono (Against.coeff (c:=(sigma p:ℝ)*s) (A:=A) (s:=s) ?_ hf) le_rfl (by linarith only) (by rfl)
    refine Against.of_words hT (fun J _ Y q hh he r=>?_) -- includes data
    have hxy:=he.windows ha pack_carries
    apply RateLE.congr (viewer_cost Z H.schedule p q hT r hx hh hxy hs hv)
    filter_upwards [(hx.mono hv|>.chorus hh (hxy.mono hv)).inject] with i hi
    change _ = readExpr D _ (tokenWord D (X i) p * tokenWord D (Y i) q)
    rw [← token_beside,read_word D M.coherent _ (spectate Z _).laws.toSymmetric (spectate_respects Z _) (spectate_ready Z _),totalObserve,if_pos hi]
  | plus _ _ hx hy=> exact Against.plus hx hy hT
  | germ _ h hx=> exact Against.ident hx h

/-- Priced expressions at this layer after incorporating subcluster (signed) approximations. -/
structure Funds (Z : Final C F S) (M : Devices Z.sector.derivatives) (φ : Filter W) (T : W→ℝ) (A : Set (W → E4)) (s c : ℝ) (e : W→ Expression Z.sector.derivatives) : Prop where
    loose : ∃ d, Fine M φ T A 1 d e
    enter : ∀ q : ℝ, ∃ E, Fine M φ T A s c E ∧ Precision Z M φ T A s q (e-E)
lemma Fine.funds (h : Fine M φ T A s c e) (hv : s ≤ 1) : Funds Z M φ T A s c e:=by refine ⟨h.increase_layer hv,fun q=>⟨_,h,?_⟩⟩; rw [sub_self]; exact Against.zero
namespace Funds
lemma zero : Funds Z M φ T A s c 0 := ⟨⟨0,.zero⟩,fun _=> ⟨_,Fine.zero,sub_zero (0:EP) ▸ Against.zero (c:=_)⟩⟩ -- direction
lemma mono (h : Funds Z M φ T A s c e) (hu : c ≤ d) (hv : A⊆A') : Funds Z M φ T A' s d e := ⟨h.loose.imp fun _ he=>he.enlarge hv, fun q=> by obtain ⟨f,h,h'⟩:= h.enter q; exact ⟨f,h.admits hu hv,h'.mono le_rfl le_rfl hv⟩⟩
lemma fits (h : Funds Z M φ T A s c e) {U : W→Set E4} (hc : ∀ x∈A,∀ᶠ i in φ,x i∈U i) : ∀ᶠ i in φ,e i∈supportedAt (U i):= h.loose.choose_spec.fits hc
lemma ident (h : Funds Z M φ T A s c e) (hx : e =ᶠ[φ] f) : Funds Z M φ T A s c f := ⟨h.loose.imp (fun _ he=> he.germ hx), fun q=> Exists.imp (fun _ he=> ⟨he.1,Against.ident he.2 (hx.sub (Eventually.of_forall fun _=> rfl))⟩) (h.enter q)⟩
lemma minus (h : Funds Z M φ T A s c e) : Funds Z M φ T A s c (-e):= by refine ⟨h.loose.imp (fun _ he=>he.minus),fun r=>?_⟩; obtain ⟨g,h,h'⟩:=h.enter r; exact ⟨-g,h.minus,(show -e - -g= -(e-g) from by abel) ▸ Against.minus h'⟩
variable (hT : Tendsto T φ atTop)
include hT
lemma plus (h : Funds Z M φ T A s c e) (h' : Funds Z M φ T A s c f) : Funds Z M φ T A s c (e+f) := by
   obtain ⟨a,ha⟩:= h.loose; obtain ⟨b,hb⟩:= h'.loose; refine ⟨⟨max a b,Fine.plus (ha.mono (le_max_left ..)) (hb.mono (le_max_right ..))⟩,fun q=>?_⟩
   obtain ⟨g,h,hp⟩:= h.enter q; obtain ⟨k,h',hq⟩:=h'.enter q; refine ⟨g+k,h.plus h',?_⟩; rw [show e+f-(g+k)= (e-g)+(f-k) from by abel]; exact Against.plus hp hq hT
lemma times (h : Funds Z M φ T A s c e) (h' : Funds Z M φ T B s d f) (hp : Cross φ T s A B) (hu : s ≤ 1) : Funds Z M φ T (A ∪ B) s (c+d) (e*f) := by
   obtain ⟨a,ha⟩:= h.loose; obtain ⟨b,hb⟩:= h'.loose; refine ⟨⟨a+b,ha.times hb (hp.mono hu)⟩,fun q=>?_⟩
   obtain ⟨g,h,hA⟩:=h.enter (q-b); obtain ⟨c',hc⟩:=h.increase_layer hu
   obtain ⟨k,h',hB⟩:=h'.enter (q-c')
   refine ⟨g*k,h.times h' hp,?_⟩; rw [show e*f-g*k=(e-g)*f+(f-k)*g from by ring]
   exact Against.plus ((sub_add_cancel q b) ▸ Against.times hA hb hp hu) ((sub_add_cancel q c') ▸ (union_comm B A ▸ Against.times hB hc hp.swap hu)) hT
omit [Fintype I] in
lemma product {p : Finset I}{A' : I→ Set (W→E4)} {X : I→W→Expression Z.sector.derivatives} {a : I→ℝ} (hu : s ≤ 1)
    (h : ∀ i∈p,Funds Z M φ T (A' i) s (a i) (X i)) (hc : (p:Set I).Pairwise (fun i j=> Cross φ T s (A' i) (A' j))) : Funds Z M φ T (⋃ i∈p,A' i) s (∑ i∈p,a i) (∏ i∈p,X i) := by
  induction p using Finset.induction_on with
  | empty => rw [Finset.sum_empty,Finset.prod_empty]; exact (Fine.unitOne hT).funds hu
  | @insert i p hi ih =>
    have hs : (p:Set I) ⊆ ↑(insert i p : Finset I) := Finset.coe_subset.mpr (Finset.subset_insert i p)
    rw [Finset.set_biUnion_insert,Finset.sum_insert hi,Finset.prod_insert hi]; refine times hT (h i (by simp)) (ih (fun j hj=> h _ (Finset.mem_insert_of_mem hj)) (hc.mono hs)) ?_ hu
    intro x hx y hy; obtain ⟨j,hj,h⟩:= Set.mem_iUnion₂.mp hy; exact hc (show i ∈ (↑(insert i p : Finset I):Set I) by simp) (hs hj) (fun h=> hi (h ▸ hj)) _ hx _ h
variable [φ.NeBot]
lemma tests (H : Services C F S) (h : Funds Z M φ T A s c e) (hs : 0 ≤ s) (hv : s ≤ v) (hu : v ≤ 1) : Against Z M φ T A s v c e:= by
   intro B hp q g hg; obtain ⟨b,hb⟩:=hg.increase_layer hu
   obtain ⟨f,h,h'⟩:=h.enter (c+q-b)
   have hX:=(h.tests (Z:=Z) hT H hs hv) hp hg
   have hY:= h' hp hb; rw [sub_add_cancel] at hY
   have hV:= View.plus hX hY hT; rwa [show e*g=f*g+(e-f)*g by ring]
lemma receipt (H : Services C F S) (h : Funds Z M φ T A s c e) (hs : 0 ≤ s) (hu : s≤1) : View Z M φ T c e := by
   have ht:= tests hT H h hs le_rfl hu (A':=∅) (fun _ _ _ hx=> by simp at hx) (Fine.unitOne hT)
   simpa only [mul_one,add_zero] using ht
end Funds
end YM.Contacts.Layers
