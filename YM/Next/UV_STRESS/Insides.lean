import YM.Cells.Tiling
import YM.Next.UV_STRESS.Bonds

/-!
# Locality/propagation support of the back kernel

Loose radii are fine (scheduling mechanism covers this one use). Keep tagged
frame choices, walks, and both endpoints even though not on representatives.
Includes wrap, frame and predictor alternatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Set Function Filter MeasureTheory  Lattice Wilson RG Cells
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

section Paths
variable (P : Patch)

private lemma box_larger {i j : ℕ} (h : i≤j) {x : Cover} (he : x ∈ box i) : x∈box j := by
  obtain ⟨A,B⟩ := box_test.mp he
  exact box_test.mpr ⟨fun i => le_trans (neg_le_neg (Nat.cast_le.mpr h)) (A i),fun i => le_trans (B i) (Nat.cast_le.mpr h)⟩

private lemma meter_walk {r : ℕ} {x : Cover} (w : Walk) (hx : x∈box r) : ∀ i ∈ visits x w, i∈box (r+w.length) := by
  induction w generalizing x r with
  | nil => intro i hi; simp [visits] at hi; subst i; simpa using hx
  | cons d l ih =>
    intro i hi; rcases List.mem_cons.mp hi with h|h
    · subst i; exact box_larger (Nat.le_add_right ..) hx
    have he : x+d.vec ∈ box (r+1) := by
      rw [box_test] at *
      have hs k : - (↑(r+1):ℤ) ≤ (x+d.vec : Cover) k ∧ (x+d.vec : Cover) k ≤ ↑(r+1 : ℕ) := by
        have hm := hx.1 k; have hn := hx.2 k
        rcases d with ⟨j,e|e⟩ <;> by_cases ht : k=j <;> simp [Step.vec,ht] at hm hn ⊢ <;> omega
      exact ⟨fun i => (hs i).1, fun i => (hs i).2⟩
    exact (show r+1+l.length=r+(d::l).length by simp; omega) ▸ ih he i h

private lemma extent (x y : P.Points) (k : Lattice.Order) : (route x.val y.val k).length ≤ 8*P.radius := by
  have he (i : Axis) : (straight i (y.val i-x.val i)).length ≤ 2*P.radius := by
    have H₁ := (box_test.mp x.property).1 i; have H₂ := (box_test.mp x.property).2 i
    have H₃ := (box_test.mp y.property).1 i; have H₄ := (box_test.mp y.property).2 i
    rw [straight,List.length_replicate]; omega
  have hv (l : List Axis) : (axisRoute x.val y.val l).length ≤ l.length*(2*P.radius) := by
    induction l with
    | nil => simp [axisRoute]
    | cons j l ih =>
      rw [show axisRoute x.val y.val (j::l)=_ ++ axisRoute x.val y.val l from rfl,List.length_append];
      apply le_trans (Nat.add_le_add (he j) ih)
      simp only [List.length_cons]; nlinarith
  calc
    _ ≤ _ := hv (allAxes k)
    _ = _ := by simp [allAxes]; omega

private lemma escort {U V : CoverConfig G} (h : Agrees (↑(box (9*P.radius))) U V)
    (x y : P.Points) (L : Lattice.Order) : travel U x.val (route x.val y.val L) = travel V x.val (route x.val y.val L) := by
  apply travel_local _ _ U V
  intro e hx he; apply h
  exacts [(box_larger (by have := extent P x y L; omega) (meter_walk _ (box_test.mpr (box_test.mp x.property)) _ hx)),
    (box_larger (by have := extent P x y L; omega) (meter_walk _ (box_test.mpr (box_test.mp x.property)) _ he))]

private lemma valid_min {U V : CoverConfig G} {C : KernelChoices} (h : Agrees (↑(box (9*P.radius))) U V) :
    P.usesMin C U ↔ P.usesMin C V := by simp only [Patch.usesMin, Patch.via,Patch.axial,escort P h]

private lemma rate_axial {U V : CoverConfig G} (h : Agrees (↑(box (9*P.radius))) U V) (t : P.FrameTag) :
    P.axialCost U t=P.axialCost V t := by
  unfold Patch.axialCost; apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro i _
  split; rename_i hy
  · unfold Patch.axial; simp_rw [escort P h, show U (x.val,i)=V (x.val,i) from
      h (x.val,i) (box_larger (by omega) x.property) (box_larger (by omega) hy)]
    rw [show travel U _ (route t.1.val (x.val+step i) t.2)=travel V _ _ from escort P h t.1 ⟨x.val+step i,hy⟩ _]
  rfl

lemma local_frame {U V : CoverConfig G} {C : KernelChoices} (h : Agrees (↑(box (9*P.radius))) U V) (t : P.FrameTag)
    (hc : P.Branches C G) : P.frameMass C U t=P.frameMass C V t ∧ P.frame C U t=P.frame C V t := by
  classical
  by_cases hh : P.usesMin C V
  · have hw := (valid_min P h).2 hh
    simp only [Patch.frameMass,Patch.frame,hw,hh,↓reduceIte,true_and]
    have he (x : P.Frame G) : P.score U x=P.score V x := by
      unfold Patch.score; simp only [Patch.via,escort P h]
    apply ExistsUnique.unique (hc.frame_unique V hh) ?_ (P.min_exists V).choose_spec
    have hp := (P.min_exists U).choose_spec
    refine ⟨hp.1,fun z hv => ?_⟩
    rw [← he, ← he]; exact hp.2 z hv
  have he := mt (valid_min P h).1 hh
  have hv : P.facesum U=P.facesum V := by
    unfold Patch.facesum; apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro p _
    split; rename_i hp
    · apply congr_arg G.chord
      apply travel_local x.val (square p.val.1 p.val.2) U V
      intro e he hf; exact h e (box_larger (by omega) (hp _ he)) (box_larger (by omega) (hp _ hf))
    rfl
  have hx : P.eligible C U=P.eligible C V := by unfold Patch.eligible; simp only [hv, rate_axial P h]
  simp only [Patch.frameMass,Patch.frame,hh,he, ↓reduceIte, hx, true_and]; unfold Patch.axial
  simp_rw [escort P h]
end Paths
section Propagation

variable {c f : Side} (S : StepData c f) (H : S.patch.Branches S.kernel G)

def shadow (A : Set (Site c)) := {y : Site f|∃ x∈ A,∃ z∈box (9*S.patch.radius),y=wrap f z+S.ratio.embed x}

lemma inside_agrees (A : Set (Site c)) (x : Site c) (hx : x∈A) (U V : Config G f) (hp : Agrees (shadow S A) U V) :
    Agrees (↑(box (9*S.patch.radius))) (expandAt (S.ratio.embed x) U) (expandAt (S.ratio.embed x) V) := by
  rintro ⟨z,i⟩ hz hi; let w := S.ratio.embed x
  apply hp (wrap f z+w,i) ⟨x,hx,z,hz,rfl⟩
  refine ⟨x,hx,z+step i,hi,?_⟩
  change wrap f z+ S.ratio.embed x + step i =_; rw [map_add,wrap_step]; abel

def edges (A : Set (Site c)) (e : Edge (Site c)) := e.1∈A ∧ e.1+step e.2∈A

lemma reads_on_edges {A : Set (Site c)} {F : Config G c → ℂ} (hp : LocalOn A F) : Draws (edges A) F :=
  fun x y h => hp x y fun i a b => h i ⟨a,b⟩

lemma fees_tags (x : Config G f) {A : Set (Site c)} {a b : S.SitesChoice} (ha : EqOn a b A) (β : ℝ) (i : Edge (Site c))
    (hi : edges A i) : fees S β x a i=fees S β x b i := by
  have ht : S.connector x a i=S.connector x b i := funext fun y => by
    simp only [StepData.connector,StepData.frames]; rw [ha hi.1,ha hi.2]
  unfold fees; simp_rw [ht]

include H in
lemma fees_input (x y : Config G f) {A : Set (Site c)} (ha : Agrees (shadow S A) x y) (t : S.SitesChoice) (β : ℝ)
    (i : Edge (Site c)) (hi : edges A i) : fees S β x t i=fees S β y t i := by
  have h (z : S.patch.Points) : travel (expandAt (S.ratio.embed i.1) x) z.val (List.replicate S.patch.L.val (posDir i.2)) =
      travel (expandAt (S.ratio.embed i.1) y) z.val (List.replicate S.patch.L.val (posDir i.2)) := by
    have ht : (S.patch.L.val) ≤ S.patch.radius := by
      unfold Patch.radius; nlinarith
    let l := List.replicate S.patch.L.val (posDir i.2)
    have hg : S.patch.radius+l.length ≤ 9*S.patch.radius := by simp only [l,List.length_replicate]; omega
    apply travel_local z.val l (expandAt (S.ratio.embed i.1) x) (expandAt (S.ratio.embed i.1) y)
    intro e he hf; apply inside_agrees S _ _ hi.1 _ _ ha
    exacts [box_larger hg (meter_walk l z.property _ he),box_larger hg (meter_walk l z.property _ hf)]
  have hX (v) (hv : v∈A) : S.frames x t v=S.frames y t v :=
    (local_frame S.patch (inside_agrees S A v hv x y ha) (t v) H).2
  have he : S.connector x t i=S.connector y t i := funext (fun v => by
    unfold StepData.connector; rw [hX _ hi.1, hX _ hi.2,h])
  unfold fees; simp_rw [he]

def forecast (β : ℝ) (U : Config G f) (B : Config G c → ℂ) (t : S.SitesChoice) : ℂ :=
    scatter G.probHaar (fees S β U t) B

lemma forecast_tags (U : Config G f) {A : Set (Site c)} {B : Config G c→ℂ} (ha : LocalOn A B) (β : ℝ) :
    Draws (·∈A) (forecast S β U B) := by
  classical
  intro x y hx
  unfold forecast
  rw [scatter_uses _ _ _ (reads_on_edges ha) (fees_total S β U x),scatter_uses _ _ (fees S β U y) (reads_on_edges ha) (fees_total S β U y)]
  apply congr_arg (fun w => scatter G.probHaar w _)
  exact funext fun i => fees_tags S U (fun _ h => hx _ h) β i i.property

include H in
lemma through (β : ℝ) {A : Set (Site c)} {B : Config G c→ℂ} (hp : Interior A B) : Interior (shadow S A) (back S β B) := by
  classical
  have ht := pulled S (borel_bounded hp) H β
  refine ⟨transfer_gauge S (borel_bounded hp) H β hp.gauge,ht.meas,?_ ,ht.cost⟩
  intro U V hu
  rw [scanned_back S β U B (borel_bounded hp),scanned_back S β V B (borel_bounded hp)]
  have hy (x) := forecast_tags S x hp.localSites β
  apply scanning_congr (·∈A) _ _ _ _ (hy U) (hy V) (channels_mass _ _ H) (channels_mass _ _ H)
  · intro i hi; funext t
    unfold channels; rw [(local_frame S.patch (inside_agrees S A i hi U V hu) t H).1]
  funext i
  unfold forecast
  rw [scatter_uses (edges A) _ _ (reads_on_edges hp.localSites) (fees_total S β U i),
    scatter_uses (edges A) _ (fees S β V i) (reads_on_edges hp.localSites) (fees_total S β V i)]
  apply congr_arg (fun w => scatter G.probHaar w _)
  exact funext fun j => fees_input S H U V hu i β j j.property
end Propagation

section Joint
variable {c f : Side} (S : StepData c f) (H : S.patch.Branches S.kernel G) (β : ℝ)

include H in
lemma back_product {A B : Set (Site c)} {u v : Config G c→ℂ} (h : Disjoint A B) (hu : Interior A u) (hv : Interior B v) :
    back S β (u*v)=back S β u * back S β v := by
  classical
  have hV := hv.enlarges (show B⊆Aᶜ from fun _ he ht => Set.disjoint_left.mp h ht he)
  have hp : Interior univ (u*v) := (hu.enlarges (subset_univ _)).times (hv.enlarges (subset_univ _))
  funext U; rw [Pi.mul_apply,scanned_back S _ _ _ (borel_bounded hu),scanned_back S _ _ _ (borel_bounded hv),
    scanned_back S _ _ _ (borel_bounded hp)]
  have hh t : forecast S β U (u*v) t=forecast S β U u t * forecast S β U v t :=
    scatter_parts _ _ _ (reads_on_edges hu.localSites) (fun s r he => hv.localSites s r (fun c hx ht => he c fun hk =>
      Set.disjoint_left.mp h (show c.1∈A from (show c.1∈A ∧ c.1+step c.2∈A from hk).1) hx)) (fees_total S β U t)
  have ht : forecast S β U (u*v)=forecast S β U u*forecast S β U v := funext hh
  change scanning _ (forecast S β U (u*v))=scanning _ (forecast S β U u)*scanning _ (forecast S β U v)
  rw [ht]; exact scanning_parts (·∈A) (channels S U) (forecast_tags S U hu.localSites β) (forecast_tags S U hV.localSites β)
    (channels_mass S U H)

include H in
lemma back_constant (v : ℂ) : back S β (fun _ : Config G c => v)=fun _ => v := by
  funext U; unfold back; rw [integral_smul_const, S.density_total H,one_smul]

lemma back_packs {ι : Type*} (s : Finset ι) (A : ι→Set (Site c)) (F : ι→Config G c→ℂ)
    (h : (s : Set ι).Pairwise (Disjoint on A)) (ht : ∀ i∈s,Interior (A i) (F i)) (hp : S.patch.Branches S.kernel G) :
    back S β (fun U => ∏ i ∈ s,F i U) = fun Q => ∏ i∈s,back S β (F i) Q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact back_constant S hp β 1
  | @insert i s hi ih =>
    have he (j) (hh : j∈s) : Interior (A j) (F j) := ht j (Finset.mem_insert_of_mem hh)
    let B := ⋃ j ∈ s, A j
    let f (U : Config G c) := ∏ j∈s,F j U
    have hv : Interior B f := Interior.combines F s fun j hh => (he j hh).enlarges (subset_iUnion₂_of_subset j hh (Subset.refl _))
    have hS : Disjoint (A i) B := Set.disjoint_left.mpr fun x hx hc => (mem_iUnion₂.mp hc).elim
      (fun j ⟨H,Hj⟩ => Set.disjoint_left.mp (show Disjoint (A i) (A j) from h (Finset.mem_insert_self ..)
        (Finset.mem_insert_of_mem H) (fun w => hi (w ▸ H))) hx Hj)
    have he := ih (h.mono (Finset.coe_subset.mpr (Finset.subset_insert ..))) he
    simp_rw [Finset.prod_insert hi]; funext U
    change back S β (F i*f) U=_
    rw [back_product S hp β hS (ht i (Finset.mem_insert_self ..)) hv]; exact congr_arg (fun w : Config G _ → ℂ => back S β (F i) U*w U) he
end Joint
end YM.Next.UVStress
