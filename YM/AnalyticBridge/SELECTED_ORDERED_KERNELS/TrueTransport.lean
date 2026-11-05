import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Tracks
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.TrueFaces
import YM.Next.FREE_KERNELS.Lifts

/-!
# Transport rows priced at arbitrary V

Port of PathsAffine/Layout/TrackBill's argument: right factors `V e`
inside the shifted chart of the true replica are constant group matrices,
not perturbations. Use *polynomial* travel price from FREE_RESOLVENT (not
exponential growth C^walk.length which could not pay the sums). No branch
differentiation in paths. Cut and uncut, actual all-length `Sheet`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Selected
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid Work.F03 Filter Function Set Work.E03
  FreeResolvent Affine TestD Mark
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {f c : Side} {k : ℕ} {σ A γ M d : ℝ}

def model (S : StepData c f) (V : Config G c) (s : Signed) (z : Vec G c 1) := pull s 0 (replica S.ratio
  (increment V (fun i => sleeve G (paint G c z i))))

private lemma right_ceiling {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → G.El} (h : Ceiling k A (G.mat ∘ F)) (u : G.El) :
    Ceiling k A (fun x => G.mat (F x*u)) := by
  let L := (ContinuousLinearMap.mul ℝ G.Mat).flip (G.mat u)
  have hp := ContinuousLinearMap.opNorm_le_bound (𝕜:=ℝ) L zero_le_one fun x : G.Mat => by
    rw [one_mul]; exact (Gauge.frob_mul_eq x _ (G.mat_mul_star u)).le
  simp_rw [G.mat_mul]; exact (h.post L).mono (mul_le_of_le_one_left ((norm_nonneg _).trans (h.op k 0 le_rfl)) hp)

lemma model_cover (V : Config G c) (k : ℕ) (S : StepData c f) (s : Signed) (b : Step) (x : Site f) :
    Ceiling k (spaceD G k) (fun v => G.mat (b.read (model S V s v) x)) := by
  have he (i : Edge (Site f)) : Ceiling k (spaceD G k) (fun v : Vec G c 1 => G.mat (replica S.ratio
      (increment V (fun i => sleeve G (paint G c v i))) i)) := by
    unfold replica
    split
    · exact (Ceiling.ceiling_const (G.mat 1)).mono (le_max_left ..)
    apply Ceiling.mono (right_ceiling ?_ _) (le_max_right ..)
    exact ((linen_price G k).choose_spec.2).pre (file 1 _) (linen_price G k).choose_spec.1 (folder ..) (file_pos G)
  have hh (d : Step) (x : Site f) : Ceiling k (spaceD G k) (fun v : Vec G c 1 => G.mat
      (d.read (replica S.ratio (increment V (fun i => sleeve G (paint G c v i)))) x)) := by
    unfold Step.read
    split
    · simp_rw [G.mat_inv]; exact star_ceiling (he _)
    exact he _
  simp_rw [model, Step.pull_read]
  exact hh _ _

lemma model_returns (V : Config G c) (S : StepData c f) (s : Signed) : model S V s =ᶠ[𝓝 0] fun B => pull s 0 (landscape S V B) := by
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds
    (show (0:Vec G c 1) ∈ {b | ‖b‖ < (filePrice G)⁻¹} by have := file_pos G; simp [show 0 < filePrice G by positivity]) ] with x hx
  have h (e : Edge (Site c)) : sleeve G (paint G c x e) = paint G c x e := Small.small_sleeve (le_of_lt hx) (e.1,coord e.2)
  unfold model landscape; simp_rw [h]

def outline (V : Config G c) (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) (i j : tile G f) (q : ℕ) (B : Vec G c 1) :=
  let p := W.row (plaqEquiv.symm i.2.1) q; if r p.2 then p.1 * element (pull s 0 (landscape S V B)) i j p.2 else 0

variable (V : Config G c)
lemma pilgrimage (k : ℕ) (S : StepData c f) (s : Signed) (w : Walk) (x : Site f) (hs : 0 < σ) :
    Ceiling k (patchMoney G k σ (spaceD G k) k * Real.exp (σ*w.length))
      (fun y : Vec G c 1 => G.mat (travel (model S V s y) x w)) := by
  constructor
  · exact travel_cd (fun b x => (model_cover V k S s b x).smooth) w x
  intro i B hi
  apply list_op (mul_nonneg (patch_nn _ _ hs (space_nn ..) k) (Real.exp_pos _).le)
  intro l v h ht
  have hh := assembled_jets (p:=B) (fun b x => (model_cover V k S s b x).smooth) (space_nn ..) hs
    (fun b x l he => (model_cover V k S s b x).bill (space_nn ..) v ht l he B) w x l (h.le.trans hi)
  exact hh.trans (mul_le_mul_of_nonneg_right (patch_le hs (space_nn ..) (h.le.trans hi)) (Real.exp_pos _).le)
lemma march (k : ℕ) (S : StepData c f) (s : Signed) (i j : tile G f) (q : RG.Slot)
    (hs : 0 < σ) : Ceiling k (elbow G k σ * Real.exp (σ*q.length)) (fun y => element (model S V s y) i j q) := by
  unfold element
  split
  · let R := patchMoney G k (σ/2) (spaceD G k) k
    let E := Real.exp (σ/2*q.walk.length)
    have hr : 0 ≤ R := patch_nn _ k (by linarith) (space_nn ..) k
    have hR : 0 ≤ R*E := mul_nonneg hr (Real.exp_pos _).le
    have ht : Ceiling k (R*E) (fun B : Vec G c 1 => G.mat (travel (model S V s B) i.1 q.walk)) := pilgrimage V k S s _ _ (half_pos hs)
    have he := ht.mul (star_ceiling ht) (connect (G:=G) i.2.2 j.2.2) hR hR
    apply he.mono; unfold elbow
    calc
      _ ≤ 2^k * (ridge G*(R*E)*(R*E)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (ridge_le i.2.2 j.2.2) hR) hR) (by positivity)
      _ = elbow G k σ*Real.exp (σ*q.walk.length) := by rw [show Real.exp (σ*q.walk.length)=E*E by
          unfold E; rw [← Real.exp_add]; congr 1; ring]; unfold elbow R; ring
      _ ≤ elbow G k σ*Real.exp (σ*q.length) := by
        exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (by
          unfold RG.Slot.length; simp) hs.le)) (elbow_nn ..)
  apply (Ceiling.ceiling_const (0:ℝ)).mono; rw [norm_zero]; exact mul_nonneg (elbow_nn ..) (Real.exp_pos _).le

def border (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) (i j : tile G f) (q : ℕ) (B : Vec G c 1) :=
  let p := W.row (plaqEquiv.symm i.2.1) q
  if r p.2 then p.1 * element (model S V s B) i j p.2 else 0

lemma border_ceiling (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) (i j : tile G f)
    (q k : ℕ) (hs : 0 < σ) :
    Ceiling k (slotPrice G k σ (W.row (plaqEquiv.symm i.2.1) q)) (border V S s W r i j q) := by
  let p := W.row (plaqEquiv.symm i.2.1) q
  by_cases h : r p.2=true
  · rw [show border V S s W r i j q = (fun B => p.1 • element (model S V s B) i j p.2) from funext fun _ => if_pos h]
    apply ((march V k S s i j p.2 hs).scale _).mono
    unfold slotPrice p; rw [Real.norm_eq_abs]; apply le_of_eq; ring
  rw [show border V S s W r i j q = (fun _ => 0) from funext fun _ => if_neg h]; apply Ceiling.mono (Ceiling.ceiling_const _)
  rw [norm_zero]; exact slot_nn _

lemma same_motion (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) :
    ∀ᶠ B in 𝓝 0, ∀ i j q, border V S s W r i j q B = outline V S s W r i j q B := by
  filter_upwards [model_returns V S s] with B h
  intro i j q; unfold border outline; rw [h]

lemma gloss (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) (i j : tile G f) (q k : ℕ)
    (hs : 0 < σ) : ContDiffAt ℝ k (outline V S s W r i j q) 0 := by
  exact (border_ceiling V S s W r i j q k hs).smooth.contDiffAt.congr_of_eventuallyEq ((same_motion V S s W r).mono fun _ h => (h i j q).symm)

section proper
variable {W : PathData G} {σ M : ℝ} (hs : 0 < σ) (hW : Sheet W σ M)
variable (S : StepData c f) (s : Signed) (r : Admit) (i j : tile G f)

include hs hW
lemma proper_motion (k : ℕ) : Ceiling k (M*elbow G k σ) (fun B : Vec G c 1 => ∑' q, border V S s W r i j q B) := by
  let T (q) := slotPrice G k σ (W.row (plaqEquiv.symm i.2.1) q)
  let u : ℕ → ℕ → ℝ := fun _ => T
  let F := border V S s W r i j
  have hf q : Ceiling k (T q) (F q) := border_ceiling V S s W r i j q k hs
  have hw : Summable T := (hW _).2.1.mul_right _
  have ht (l : ℕ) : (l:ℕ∞) ≤ (k:ℕ) → Summable (u l) := fun _ => hw
  have he (l q : ℕ) (B) (h : (l:ℕ∞) ≤ (k:ℕ)) : ‖iteratedFDeriv ℝ l (F q) B‖ ≤ u l q :=
    (hf q).op l B (by exact_mod_cast h)
  have hg q : ContDiff ℝ ((k:ℕ∞):ℕ∞ω) (F q) := (hf q).smooth
  constructor
  · exact contDiff_tsum hg ht he
  intro l B hl
  have hh : (l:ℕ∞) ≤ (k:ℕ∞) := by exact_mod_cast hl
  rw [iteratedFDeriv_tsum_apply hg ht he hh B]
  have hy := Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => he l i B hh) hw
  apply (norm_tsum_le_tsum_norm hy).trans ((hy.tsum_le_tsum (fun i => he l i B hh) hw).trans ?_)
  unfold u T slotPrice; rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right (hW _).2.2 (elbow_nn ..)

omit hs hW in
lemma written : (fun B => ∑' q, border V S s W r i j q B) =ᶠ[𝓝 0] (fun B => (over (NoHole.pathRows S s W r) V) B i j) := by
  filter_upwards [same_motion V S s W r] with x h; exact tsum_congr (h i j)

lemma path_smooth (k : ℕ) : ContDiffAt ℝ k (over (NoHole.pathRows S s W r) V) 0 := by
  apply TestD.rectangle_smooth; intro i j
  exact (proper_motion V hs hW S s r i j k).smooth.contDiffAt.congr_of_eventuallyEq (written V (W:=W) S s r i j).symm

lemma polar_motion {τ : Type*} (l : List τ) (v : τ → Vec G c 1) :
    HasSum (fun q => jet v (outline V S s W r i j q) l 0) (jet v (over (NoHole.pathRows S s W r) V) l 0 i j) := by
  let k := l.length
  let F := border V S s W r i j
  let f := fun B => ∑' q, F q B
  let T (q) := slotPrice G k σ (W.row (plaqEquiv.symm i.2.1) q)
  let u : ℕ → ℕ → ℝ := fun _ => T
  have hf q : Ceiling k (T q) (F q) := border_ceiling V S s W r i j q k hs
  have hw : Summable T := (hW _).2.1.mul_right _
  have ht (l : ℕ) : (l:ℕ∞) ≤ (k:ℕ∞) → Summable (u l) := fun _ => hw
  have he (l q : ℕ) (B) (h : (l:ℕ∞) ≤ (k:ℕ∞)) : ‖iteratedFDeriv ℝ l (F q) B‖ ≤ u l q :=
    (hf q).op l B (by exact_mod_cast h)
  have hg q : ContDiff ℝ ((k:ℕ∞):ℕ∞ω) (F q) := (hf q).smooth
  rw [← TestD.entry v l (path_smooth V hs hW S s r k) i j, ← identical v (written V (W:=W) S s r i j) l]
  have hh : HasSum (fun q => iteratedFDeriv ℝ k (F q) 0) (iteratedFDeriv ℝ k f 0) := by
    rw [iteratedFDeriv_tsum_apply hg ht he (k:=k) le_rfl 0]
    exact (Summable.of_norm_bounded hw (fun q => he k q 0 le_rfl)).hasSum
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Vec G c 1) ℝ (v ∘ l.get)
  have h1 : HasSum (fun q => jet v (F q) l 0) (jet v f l 0) := L.hasSum hh
  have h2 (q : ℕ) : jet v (outline V S s W r i j q) l 0=jet v (F q) l 0 := identical v (A:=outline V S s W r i j q) (B:=F q) ((same_motion V S s W r).mono fun _ h => (h i j q).symm) l
  simp_rw [h2]; exact h1
end proper
lemma motion_local (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) (i j : tile G f)
    (q : ℕ) :
    let w := (W.row (plaqEquiv.symm i.2.1) q).2.walk
    outline V S s W r i j q=outline V S s W r i j q ∘ (coarse G (named S s i) w.length) := by
  intro w; ext B
  have ht : travel (pull s 0 (landscape S V B)) i.1 w = travel (pull s 0 (landscape S V ((coarse G (named S s i) w.length) B))) i.1 w := by
    rw [travel_pull, travel_pull]
    refine Next.Fluctuations.travel_near S.ratio.parent (parent_step S) _ _ _ _ w.length (by simp) ?_
    exact fun e he => (landscape_local S V (named S s i) w.length (B,0) e he).symm
  simp only [Function.comp_apply, outline, element]; rw [ht]

lemma motion_slot (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) (i j : tile G f)
    (q : ℕ) :
    let R := (W.row (plaqEquiv.symm i.2.1) q).2
    outline V S s W r i j q ≠ 0 → j.1=wrap f R.offset+i.1 := by
  intro R; contrapose!
  intro h; funext; simp only [outline,element]; split
  · rw [if_neg]; · simp
    intro he; exact h (congr_arg Prod.fst he)
  rfl

lemma on_motion (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) (i j : tile G f)
    (q : ℕ) {l : List (raw G c)} (he : jet (ray G c) (outline V S s W r i j q) l 0 ≠ 0) :
    let p := (W.row (plaqEquiv.symm i.2.1) q).2
    separation (named S s i) (named S s j) ≤ p.length ∧ ∀ x ∈ l, separation (named S s i) (hearth x) ≤ p.length := by
  intro p
  have hh : p.walk.length ≤ p.length := Nat.le_add_right ..
  constructor
  · have hi : outline V S s W r i j q ≠ 0 := fun hv => he (by rw [hv, zero_null])
    have hv := motion_slot V S s W r i j q hi
    apply le_trans _ hh
    unfold named; rw [move_separates, show j.1=stop i.1 p.walk from ?_]; exact Work.E03.sep_walk _ (parent_step S) ..
    have hr : stop i.1 p.walk=wrap f p.offset+i.1 := by
      unfold RG.Slot.offset
      rw [wrap_stop_cover,map_zero,add_comm,← Work.E03.stop_add_left]; simp
    exact hv.trans hr.symm
  intro x hx
  exact (peel l hx (t:=fun x => separation (named S s i) (hearth x) ≤ p.walk.length)
    (EventuallyEq.of_eq (motion_local V S s W r i j q)) (gloss V S s W r i j q l.length (by norm_num : (0:ℝ)<1)) he).trans hh

lemma transport_entry (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) (i j : tile G f)
    (q k : ℕ) (hs : 0 < σ) (l : List (raw G c)) (hl : l.length ≤ k) (hd : 0 ≤ d) (hg : 0 ≤ γ)
    (hv : γ+2*k*d ≤ σ/2) (R : ℕ) (hR : ∀ z, r z=true → R ≤ z.length) :
    let P := facetReserve W i q
    let C := Real.exp (-(σ/4)*R) * ((|P.1| * Real.exp (σ*P.2.length))*elbow G k (σ/4))
    let a := |jet (ray G c) (outline V S s W r i j q) l 0|
    let b := (native c).weight γ (named S s i) (named S s j)*a
    (marks G c d).pay l (named S s i)*b ≤ C ∧ (marks G c d).pay l (named S s j)*b ≤ C := by
  intro P C a b
  by_cases he : jet (ray G c) (outline V S s W r i j q) l 0=0
  · have hh : b=0 := by unfold b a; rw [he,abs_zero,mul_zero]
    have hc : 0 ≤ C := mul_nonneg (Real.exp_pos _).le (mul_nonneg (by positivity) (elbow_nn ..))
    simp only [hh,mul_zero,hc,and_self]
  have hc : outline V S s W r i j q≠0 := fun h => he (by rw [h,zero_null])
  have ht : r P.2=true := by
    by_contra hh; apply hc
    funext B
    exact if_neg hh
  let x := named S s i; let y := named S s j; let L : ℝ := P.2.length
  obtain ⟨h1,h2⟩ := on_motion V S s W r i j q he
  have hL : (native c).d x y ≤ L := by
    change ((separation _ _):ℝ) ≤ ((P.2.length:ℕ):ℝ); exact_mod_cast h1
  have hm (t : raw G c) (h : t∈l) : (native c).d x (hearth t) ≤ L := by
    change ((separation _ _):ℝ) ≤ ((P.2.length:ℕ):ℝ); exact_mod_cast h2 t h
  have hn : 0 ≤ L := by unfold L; positivity
  have hK (z : Site c) (hz : (native c).d z x ≤ L) : (marks G c d).pay l z*b ≤ C := by
    have hh t (h : t∈l) : (native c).d z (hearth t) ≤ 2*L := le_trans ((native c).triangle z x _) ((add_le_add hz (hm t h)).trans_eq (two_mul L).symm)
    have h5 := border_ceiling V S s W r i j q k (by linarith : 0 < σ/4)
    have ha : a ≤ |P.1| * Real.exp (σ/4*L)*elbow G k (σ/4) := calc
      a = ‖jet (ray G c) (border V S s W r i j q) l 0‖ := by
        unfold a
        rw [identical _ (show border V S s W r i j q=ᶠ[𝓝 0] outline V S s W r i j q from
          (same_motion V S s W r).mono fun _ h => h i j q)]; rfl
      _ ≤ _ := h5.bill (slot_nn _) (ray G c) ray_nn l hl 0
    refine (mul_le_mul (plumb (native c) z hearth l hd _ hh)
      (mul_le_mul (Real.exp_monotone (mul_le_mul_of_nonneg_left hL hg)) ha (abs_nonneg _) (Real.exp_pos _).le)
      (show 0 ≤ b from mul_nonneg ((native c).weight_nn ..) (abs_nonneg _)) (Real.exp_pos _).le).trans ?_
    have hA : (l.length:ℝ)*d*(2*L)+γ*L+σ/4*L ≤ -(σ/4)*R+σ*L := by
      have hu : (R:ℝ) ≤ L := by unfold L; exact_mod_cast hR _ ht
      have hi : (l.length:ℝ) ≤ (k:ℝ) := by exact_mod_cast hl
      nlinarith only [mul_le_mul_of_nonneg_right hv hn, mul_le_mul_of_nonneg_left hu hs.le,
                        mul_le_mul_of_nonneg_right hi (mul_nonneg hd hn)]
    apply le_trans _ (le_trans (mul_le_mul_of_nonneg_left (Real.exp_monotone hA) (mul_nonneg (abs_nonneg P.1) (elbow_nn G k (σ/4)))) ?_)
    · simp only [Real.exp_add]; exact le_of_eq (by ring)
    unfold C L; rw [Real.exp_add]; exact le_of_eq (by ring)
  exact ⟨hK x (by rw [Cost.self]; exact hn), hK y (by rw [Cost.comm]; exact hL)⟩

theorem transport_rows (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) (k : ℕ)
    (hs : 0 < σ) (hW : Sheet W σ M) (hm : 0 ≤ M)
    (hd : 0 ≤ d) (he : 0 < γ) (hh : 2*γ+2*k*d ≤ σ/2)
    (R : ℕ) (hR : ∀ z, r z=true → R ≤ z.length) :
    Bundle (ray G c) (marks G c d) (native c) (named S s) (named S s) (over (NoHole.pathRows S s W r) V) 0 k γ
      (torusPay (Co S.patch.L (PAC G 2)) γ * (Real.exp (-(σ/4)*R)*(M*elbow G k (σ/4)))) := by
  have hz := elbow_nn G k (σ/4)
  refine ⟨path_smooth V hs hW S s r k,fun l hl => ?_⟩
  let X := (over (NoHole.pathRows S s W r) V)
  let C := Real.exp (-(σ/4)*R)
  have hc : 0 < C := Real.exp_pos _
  let B := elbow G k (σ/4)
  let H := C*(M*B)
  have hN : 0 ≤ H := mul_nonneg hc.le (mul_nonneg hm hz)
  let a := named S s (G:=G) (r:=2)
  let D := native c
  let Y := jet (ray G c) X l 0
  have hp (i j : tile G f) : (marks G c d).pay l (a i)*(D.weight (2*γ) (a i) (a j) * |Y i j|) ≤ H ∧
      (marks G c d).pay l (a j)*(D.weight (2*γ) (a j) (a i) * |Y i j|) ≤ H := by
    let P (q : ℕ) := facetReserve W i q
    have he (q : ℕ) := transport_entry V S s W r i j q k hs l hl hd (mul_nonneg (by norm_num) he.le) hh R hR
    let w := fun q => C*((|(P q).1| * Real.exp (σ*(P q).2.length))*B)
    have h : RG.SumBudget (fun q => |(P q).1| * Real.exp (σ*(P q).2.length)) M := hW _
    have hw : Summable w := (h.2.1.mul_right B).mul_left C
    have hw' : (∑' q, w q) ≤ H := by
      unfold w; rw [tsum_mul_left,tsum_mul_right]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h.2.2 hz) hc.le
    let F q := jet (ray G c) (outline V S s W r i j q) l 0
    have hb : HasSum F (Y i j) := polar_motion V hs hW S s r i j l _
    let L := D.weight (2*γ) (a i) (a j)
    have hh (d : ℝ) (hd : 0 < d) (hy : ∀ q, d*(L*|F q|) ≤ w q) : d*(L*|Y i j|) ≤ H := by
      have hL : 0 < L := D.weight_pos ..
      let g q := ‖(d*L)*(F q)‖
      have ht (q) : g q=d*(L*|F q|) := by unfold g; simp [Real.norm_eq_abs,abs_of_pos hL,abs_of_pos hd,mul_assoc]
      have hs : Summable g := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => (ht i).trans_le (hy _)) hw
      have he := le_trans (norm_tsum_le_tsum_norm hs) ((hs.tsum_le_tsum (fun i => (ht i).trans_le (hy _)) hw).trans hw')
      rw [(hb.mul_left (d*L)).tsum_eq] at he
      simpa only [Real.norm_eq_abs,abs_mul,abs_of_pos hd,abs_of_pos hL,mul_assoc] using he
    constructor
    · exact hh _ (pay_pos ..) fun q => (he q).1
    rw [Cost.weight_symm]; exact hh _ (pay_pos ..) fun q => (he q).2
  have ht := named_volume S s 2 _ he (G:=G)
  nth_rw 1 [show γ=2*γ-γ by ring] at ht
  exact Bill.of_entry ht ht hN (fun i j => (hp i j).1) fun i j => (hp i j).2

end YM.SelectedOrderedKernels.Selected
