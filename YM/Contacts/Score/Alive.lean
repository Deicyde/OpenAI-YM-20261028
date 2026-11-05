import YM.Contacts.Score.InPatch

/-! # Germs in the punctured formulas

Punctured score may read a test at different positions from its argument, so that
pointwise equality on the open stratum is not the justification for splitting the integral
in shells. It will suffice to have eventually exact equality of the **germs** throughout
the punctured plane when reconstructing from partial shell sums. We need the assumption that this
is done in a genuine normal direction in the ambient plane; we do not assert that this operation
applies to restrictions at a point of total collapse.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Normal
open Function Filter Set Metric MeasureTheory Submodule Ordered MultipleContact MultipleContact.Script
open scoped Topology BigOperators Classical ContDiff TensorProduct InnerProductSpace
variable {k : ℕ} {E F : Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable [CommRing F] [Algebra ℂ F] {p q : Optical E} {K L : Submodule ℝ E}

/-- Germ transformation preserving a test gauge between any two centers. -/
def Adhesive (k : E→ₗ[ℝ] E4)(p : Optical E) : Prop:= ∃ f:E→E,Germ p f∧∀ x,k (f x)=k x
variable {D : E→ₗ[ℝ] E4}
namespace Adhesive
lemma of_track (h : Germ p (slide K 0))(hp : K ≤ D.ker) : Adhesive D p:= by refine ⟨_, h, fun x=>?_⟩; rw [slide_zero,map_sub, show D (K.starProjection x)=0 from hp (K.starProjection_apply_mem x), sub_zero]
omit [FiniteDimensional ℝ E] in
lemma multiply (h : Adhesive D p)(k : Adhesive D q): Adhesive D (p*q):= by obtain ⟨f,hf,h⟩:=h; obtain ⟨k,hk,ha⟩:=k; exact ⟨_,hf.times hk,fun x=> (ha (f x)).trans (h x)⟩
lemma from_use (h : Uses K p)(hp : K≤ D.ker) : Adhesive D p:= by
   induction h with
   | id=> exact ⟨_,Germ.identity,fun _=>rfl⟩
   | times _ _ hx hy=> exact hx.multiply hy
   | taylor L h s i=> exact of_track (focal s i) (h.trans hp)
omit [FiniteDimensional ℝ E] in
lemma fixed {D : E →ₗ[ℝ] E4} {I : Type} (s : Finset I)(p : I → Score E F)
     (hc : (s:Set I).Pairwise fun i j=> Commute (p i) (p j)) (h : ∀ i∈s, Mark (Adhesive D) (p i)): Mark (Adhesive D) (product s p) := by
   rw [actual s p hc]; exact Finset.noncommProd_induction _ _ _ (Mark (Adhesive D)) (fun x y hx hy=> hx.prod hy fun a b h k=> Adhesive.multiply h k) (Mark.inst (A:=F) ⟨_,Germ.identity,fun _=>rfl⟩) h -- uses multiply [finite] omit issue
omit [FiniteDimensional ℝ E] in
lemma reads {I:Type*}{p : Score E F}(h : Mark (Adhesive D) p) {f : I → SmoothTests E}{g : SmoothTests E}{φ:Filter I}
    (hT : ∀ x,D x≠0 → ∀ᶠ i in φ,(f i).val =ᶠ[𝓝 x] g.val) {x:E}(hx:D x ≠ 0): ∀ᶠ i in φ, action x (f i) p=action x g p := by
    induction h with
    | atom t h=> obtain ⟨f,h,hf⟩:=h; filter_upwards [hT _ ((hf x).symm ▸ hx)] with i hi; simp only [action_tmul]; exact congrArg (· • t x) (h x _ _ hi|>.eq_of_nhds)
    | zero=> simp
    | plus _ _ hx hy=> filter_upwards [hx,hy] with i hx hy; rw [map_add,map_add,hx,hy]
end Adhesive

variable (P : E →ₗᵢ[ℝ] Points k)
/-- linear in the positions. Shifts may change the gauge by a constant, no offsets within the
same group are needed here. -/
def detector (u v : Group k) : E→ₗ[ℝ] E4:= (centroid u-centroid v).toLinearMap.comp P.toLinearMap
omit [FiniteDimensional ℝ E] in
lemma in_detector {A B q : Group k}(hA : q=A ∨ Disjoint q A)(hB : q=B ∨ Disjoint q B) : normalOn P q ≤ (detector P A B).ker := by
    intro x hx; have hu(a : Group k)(he : q=a ∨ Disjoint q a):centroid a (P x)=0:= by
      rcases he with rfl|he; exact ((on_plane ..).1 hx).1
      rw [centroid_formula]; have hi p (hp:p∈a) : P x p=0:= (plane_iff.mp ((on_plane ..).1 hx)).2 _ (fun h=>Finset.disjoint_left.mp he h hp); rw [Finset.sum_eq_zero hi,smul_zero]
    exact sub_eq_zero.mpr ((hu A hA).trans (hu B hB).symm)
namespace System
variable {A : Type} {g : Group k} (s : ℝ) (T : System E (Grammar A) k)
variable (Q : Pieces g)(i : Q.parts)
local notation "𝒫" => Pieces i.val
lemma adhesion (R : 𝒫) (u v:R.parts) (F : E→ Grammar A→ₗ[ℂ] Grammar A): Mark (Adhesive (detector P u.val v.val))
      (T.portionAt P s Q i (reshape F (parcel (T.cumulant P s) R))):= by
    let d:= detector P u.val v.val; apply Mark.prod (R:= Adhesive d) (T:=Adhesive d) (S:=Adhesive d) ?_ ?_ (fun _ _ ha hb=> ha.multiply hb)
    · apply Adhesive.fixed; exact ((T.knowTags P s).stands Q).mono (Finset.coe_subset.mpr (Finset.erase_subset ..))
      intro q h; obtain ⟨hh,hq⟩:= Finset.mem_erase.mp h; have he : Disjoint q i.val := Q.disjoint hq i.property hh; exact ((T.uses_full P s q).relabel (tag q)).switch (fun l ht=> Adhesive.from_use ht (in_detector P (.inr (Disjoint.mono_right (R.le u.property) he)) (.inr (Disjoint.mono_right (R.le v.property) he))))
    refine Mark.relabel (Mark.transformed (Adhesive.fixed R.parts (T.cumulant P s) ((T.compatible P s).stands R) ?_) _) _
    intro q hq; have hh(a:R.parts) : q=a.val ∨ Disjoint q a.val:= (Or.elim (Classical.em (q=a.val)) Or.inl fun he=>Or.inr (R.disjoint hq a.property he)); exact (T.translatesOrigin P s q).switch (fun l hl=> Adhesive.of_track hl (in_detector P (hh u) (hh v)))

lemma precursors (Y : E→ Grammar A→ₗ[ℂ] Grammar A) : T.opensRoot P s Q i Y=
     ∑ R∈(Finset.univ.erase (⊤:Pieces i.val)), T.portionAt P s Q i (reshape Y (parcel (T.cumulant P s) R)):= by
   unfold opensRoot portionAt punctured receding; rw [map_sum,map_sum,Finset.mul_sum]
variable (hp : plane i.val ≤ LinearMap.range P.toLinearMap)
include hp
lemma reaches [MeasureSpace E][BorelSpace E][(volume: Measure E).IsAddHaarMeasure] {I : Type*}(Y : E→ Grammar A→ₗ[ℂ] Grammar A) {f : I → SmoothTests E} {a : SmoothTests E} {φ: Filter I} (h : ∀ x:E,(normalOn P i.val).starProjection x≠0→∀ᶠ t in φ,(f t).val =ᶠ[𝓝 x] a.val) :
     ∀ᵐ x:E,∀ᶠ t in φ, action x (f t) (T.opensRoot P s Q i Y)= action x a (T.opensRoot P s Q i Y) := by
   let p : Finset (Pieces i.val):= Finset.univ.erase ⊤; let n(R : Pieces i.val):= T.portionAt P s Q i (reshape Y (parcel (T.cumulant P s) R))
   have ht (R) (hr:R∈ p) : ∀ᵐ x:E,∀ᶠ t in φ, action x (f t) (n R)= action x a (n R):= by
      obtain ⟨u,hu,v,hv,he⟩:= many (show R≠ ⊤ from (Finset.mem_erase.mp hr).1) (Q.nonempty_of_mem_parts i.property)
      have hU:=R.nonempty_of_mem_parts hu; have hV:=R.nonempty_of_mem_parts hv; let d:= detector P u v
      filter_upwards [ae_unequal hU hV (R.disjoint hu hv he) (R.subset hu) (R.subset hv) hp] with x hx
      refine Adhesive.reads (adhesion P s T Q i R ⟨u,hu⟩ ⟨v,hv⟩ Y) (fun x hD=> h x ?_) (fun H=> hx (sub_eq_zero.mp H))
      intro hh; have he : Collapsed i.val (P x):= (local_collapse hp x).mpr hh
      apply hD; apply sub_eq_zero.mpr; exact (centroid_same hU _ _ (fun a ha=> he _ (R.le hu ha))).trans ((centroid_same hV _ _ (fun a ha=> he _ (R.le hv ha))).symm)
   filter_upwards [(eventually_all_finset p).mpr ht] with x hx; filter_upwards [(eventually_all_finset p).mpr hx] with t ht; rw [precursors, map_sum,map_sum]; exact Finset.sum_congr rfl ht
end System
end YM.Contacts.Normal
