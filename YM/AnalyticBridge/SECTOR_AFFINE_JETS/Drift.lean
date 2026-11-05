import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Orientation
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Parcel
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Tracks
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Weak
import YM.Next.FREE_KERNELS.Amend


/-!
# Fixed (pre-frozen application) term of the selected affine source

Apply valuation estimates to *extensions* of the real rows. Require
value agreement on the actual V flags region for these fixed costs,
not germ identity with the system which parses flags or selectors when
perturbing V there!
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine.Offset

open Filter Function Lattice Wilson RG Precision Pressure Tree Exterior Bloch
open YM.Next YM.Next.Fluctuations YM.Next.SectorChange YM.Next.SectorChange.Rows YM.Next.SectorChange.Motion
open YM.FreeResolvent (Mark Bundle native Cost)
open YM.FreeResolvent.TestD
open YM.Push.Uniform (bolt Allows Requests travelCost)
open YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented
open YM.ProjectorNext.Equivariance (pull_formula bonds send_formula)
open YM.Work
open Pressure.Tube
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {R k n L : ℕ} {C M σ d s t x r κ : ℝ} {S : StepData c f} {A : Stores S} {F : Forest S.ratio}

section masks
variable (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices)

/-- Replace thinned data by the good-output extension on v,w. -/
def fixedF (o : Signed) (i : Twin f) : G.Color :=
  T.Xf (Stores.till x) (facade S o V 0) i -
    Pressure.zip (T.Φ (Stores.till x) (pull o 0 V)) (T.Xn (Stores.till x) (pull o 0 V)) i

def zNoise (o : Signed) (i : Bond c) : G.Color := Z S (S.prediction (facade S o V 0) (choice o k)) (pull o 0 V) i

def fixedI (o : Signed) (i : Bond c) : G.Color :=
  zNoise V k o i - Pressure.zip (T.Φ' (Stores.till x) (pull o 0 V)) (T.Xn (Stores.till x) (pull o 0 V)) i

def fixedBase (i : Slots S) : G.Color := i.2.elim (fun v => fixedF T x V i.1 v) (fun v => fixedI T x V k i.1 v)

lemma correct_base (G : Gauge) (P : Patch) (Pt : Teller G) : ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T →
    ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c), A.flags=RG.flags (temp x) V → ∀ k : S.Choices,
      Rows.restrict x (shots S x) A F (fixedBase T x V k) = Rows.restrict x (shots S x) A F (base T x V k) := by
  filter_upwards [small_span P, E04.eventually_room 0 Pt.below.clip.relaxation Pt.below.clip.radius_pos] with x hx ht
  simp_rw [add_zero] at ht
  intro c f S T hS hP A F V h k
  funext i; unfold Rows.restrict; split
  next hi =>
    apply congr_arg (slip • ·)
    rcases i with ⟨o,i|i⟩
    · have hv := Offset.guard V h (.inl i.1) o (hS.symm ▸ hx) (F:=F) hi
      change fixedF T x V o i = faceFixed T x o V i
      unfold fixedF faceFixed Mv Pressure.zip
      apply congr_arg; refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : separation (S.ratio.parent i.1.1) j.1.1 ≤ Stores.till x
      · rw [kept_vision hP ht _ (S.ratio.parent i.1.1) j hv _]
        omega
      rw [leap_bound (T:=T) _ _ _ h]; simp
    have hv := Offset.guard V h (.inr i) o (hS.symm ▸ hx) (F:=F) hi
    change fixedI T x V k o i = noiseFixed x V k o i (T:=T)
    unfold fixedI zNoise noiseFixed Mw Pressure.zip
    apply congr_arg; refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : separation i.1 j.1.1 ≤ Stores.till x
    · rw [kept_vision hP ht _ i.1 j hv _]; omega
    rw [kick_bound (T:=T) _ _ _ h]; simp
  rfl
end masks

section coords
abbrev pulse (x : ℝ) (V : Config G c) := fun z : PriceCoords G c => field V (temp x • z)

lemma coarse_pull_support (o : Signed) (V : Config G c) (i : Bond c) :
    Requests Set.univ (fun z => pull o 0 (field V z) i) coordRoot (o.act i.1) 1 := by
  intro u _ v _ h
  let j := bonds o (0:Site c) i
  have he : separation (o.act i.1) j.1 ≤ 1 := by
    unfold j; rw [send_formula]; simp only [affine,add_zero]; split
    next hh =>
      rw [separation_comm]; have hh := (E03.sep_step ((o.act i.1:Site c)-step (o.perm i.2)) (o.perm i.2)); rw [sub_add_cancel] at hh; exact hh
    next hh => simp
  have hv : field V u j=field V v j := field_dep (fun _ _ => rfl) h j he
  simp only [pull_formula]; split
  · exact congr_arg (fun g : G.El => g⁻¹) hv
  exact hv

lemma field_letters (G : Gauge) (n : ℕ) : ∃ C : ℝ, 0<C ∧ ∀ {c f : Side} (S : StepData c f)
    (V : Config G c) (o : Signed),
    let Q := fun y => pull o 0 (field V y)
    Letters Q o.act n C ∧ Letters (fun y => replica S.ratio (Q y)) (o.act ∘ S.ratio.parent) n C := by
  obtain ⟨r,C,hr,hC,h⟩ := coordinates G n
  let M := max C G.colorScale
  refine ⟨M,hC.trans_le (le_max_left ..),?_⟩
  intro c f S V o Q
  have hh := h (0:PriceCoords G c) (by rw [norm_zero]; exact hr.le) V
  have hf : Letters Q o.act n M := by
    refine ⟨fun i j => by rw [separation_signed]; exact E03.sep_step ..,coarse_pull_support o V,fun i => ?_⟩
    apply Allows.mono (C:=C) _ (le_max_left ..); unfold Q; simp_rw [pull_formula]; split
    · exact (hh.1 _).inverse (f:=fun y => field V y (bonds o 0 i))
    exact hh.1 _
  refine ⟨hf,⟨fun i j => by simp only [Function.comp_apply,separation_signed]; exact E03.parent_step ..,fun i => ?_,fun i => ?_⟩⟩
  · unfold replica; split
    · exact fun _ _ _ _ _ => rfl
    exact hf.use _
  unfold replica; split
  · exact Push.Uniform.allows_const _ ((mat_paid _).le.trans (le_max_right ..))
  exact hf.through _
end coords
section pricing
lemma z_priced (G : Gauge) (P : Patch) (K : KernelChoices) (hb : P.Branches K G) (n : ℕ) {C : ℝ} (hC : 0 ≤ C) (d : ℝ) (hd : 0<d) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K → 100*(1+radiusB x) ≤ c.val →
    ∀ (F : Forest S.ratio) (A : Stores S) (V : Config G c), A.flags=RG.flags (temp x) V → ∀ (o : Signed) (i : Bond c),
    curb (shots S x) A F x o (.inr i) → ∀ k : S.Choices, Letters (fun y => pull o 0 (field V y)) o.act n C →
      Point 0 (o.act i.1) d n (fun z => zNoise (pulse x V z) k o i) (M*fiery G x P.L) := by
  obtain ⟨r,M,hr,hM,h⟩ := chosen_branch G P K hb n
  obtain ⟨D,hD,H⟩ := secure_noise G P K hb
  let N := Real.sqrt K.penalty * (curvatureCost G * ((2:ℝ)^n*C*M))
  have hn : 0 ≤ N := mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (curvature_nn _) (by positivity))
  let K' := max (2*N) (2*D); let E := Real.exp (n*d*(predReach P+1:ℕ))
  have he : 0<K' := lt_of_lt_of_le (by linarith : 0<2*D) (le_max_right ..)
  refine ⟨E*K',mul_pos (Real.exp_pos _) he,?_⟩
  filter_upwards [h,H,small_span P,monitors G P.L] with x hx hl hy ht
  intro c f S hP hK hF F A V hv o i hi k hW
  obtain ⟨hp,hv',hh⟩ := ht
  have hw : secure x (radiusB x) i.1 (pull o 0 V) := Offset.guard V hv _ _ (hP.symm ▸ hy) hi
  let s := temp x; let u := zNoise (S:=S) (G:=G); let t := fiery G x P.L
  have hz : ‖u V k o i‖ ≤ K'*t := by
    unfold u zNoise
    rw [fixed_facade,← Identity.top_copy]
    apply (hl S hP hK hF i (pull o 0 V) hw _).trans
    apply le_trans (mul_le_mul_of_nonneg_left hh hD.le); rw [show D*(2*t)=2*D*t by ring]
    refine mul_le_mul_of_nonneg_right (le_max_right ..) (temp_nonneg _)
  let V' (y : PriceCoords G c) := u (field V y) k o i
  have h₀ : Through n V' 0 N := by
    let Q := fun z : PriceCoords G c => S.prediction (facade S o (field V z) 0) (choice o k) i
    have he := allows_first_slice ((hx S hP hK hF F A V hv o i 0 hi (by simp [hr.le])).1 (choice o k))
    have hb := (hW.through i).times (he.inverse (f:=Q))
    have h := (curvature_price (U:=fun y => pull o 0 (field V y) i*(Q y)⁻¹) hb).smul (Real.sqrt K.penalty)
    rw [abs_of_nonneg (Real.sqrt_nonneg _)] at h
    unfold V' u zNoise Z; rw [hK]
    exact Through.control h
  rw [mul_assoc]
  apply Point.of_support (R:=predReach P+1) (Through.contract h₀ hp.le hv' (show ‖V' 0‖ ≤ K'*t by unfold V'; rwa [field_zero]) ?_) _ hd.le
  rotate_left
  · intro y _ z _ he
    have hL := Letters.scaled_use (coarse_pull_support o V i) s  y (Set.mem_univ _) z (Set.mem_univ _)
      (fun j hj => he j (by omega))
    have hS : S.patch.Branches S.kernel G := by rw [hP,hK]; exact hb
    have hL' := prediction_near_eq hS (facade S o (pulse x V y) 0) (facade S o (pulse x V z) 0) (choice o k) i
      (facade_dep ?_ (fun _ _ => rfl))
    · dsimp only [pulse,V',u,zNoise,Z] at *
      rw [hL']; change _ • G.curvature (pull o 0 (field V (s • y)) i*_) = _; rw [hL]
    rw [hP]; exact field_dep (fun _ _ => rfl) (fun j hj => by change s • y j=s • z j; rw [he _ hj])
  calc N * temp x ≤ N*(2*t) := mul_le_mul_of_nonneg_left hh hn
       _ = 2*N*t := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left ..) (temp_nonneg _)
end pricing

-- Apply simultaneously. Even after cut keep all channel multiplicities.

lemma base_cost (G : Gauge) (P : Patch) (Pt : Teller G) (hP : P.Branches Pt.bind G) (n : ℕ) :
    ∃ d N : ℝ, 0<d ∧ 0<N ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T → 100*(1+radiusB x) ≤ c.val →
    ∀ (F : Forest S.ratio) (A : Stores S) (V : Config G c), A.flags=RG.flags (temp x) V → ∀ k : S.Choices,
    Parcel 0 (Wisps.down S) d n (fun z => tape.symm
      (Rows.restrict x (shots S x) A F (fixedBase T x (pulse x V z) k))) (N*fiery G x P.L) := by
  obtain ⟨C,hC,h⟩ := field_letters G n
  obtain ⟨D,hD,hE⟩ := secure_faces P G
  obtain ⟨d,M,hd,hM,h₁⟩ := bound_plotted G Pt.top.width_pos n (L:=Pt.top.paths) Pt.top.clip hC.le
    (show 0<2*D by positivity)
  obtain ⟨d',M',hd',hM',h₂⟩ := bound_plotted G Pt.below.width_pos n (L:=Pt.below.paths) Pt.below.clip hC.le (by norm_num : (0:ℝ)<2)
  obtain ⟨r,U,hr,hU,h₃⟩ := wide G Pt P.L n C M' hC.le hM'
  obtain ⟨r',U',hr',hU',h₄⟩ := noise G Pt n C M' hC.le hM'
  let a := min d d'; let b := min r r'; let s := min a b
  have hs : 0<s := lt_min (lt_min hd hd') (lt_min hr hr')
  obtain ⟨K,hK,h₅⟩ := z_priced G P Pt.bind hP n hC.le s hs
  have h₀ : 0 < max (M+U) (K+U') := lt_of_lt_of_le (add_pos hM hU) (le_max_left ..)
  let E := slip*max (M+U) (K+U')
  have he : 0<E := mul_pos slip_pos h₀
  refine ⟨s,E,hs,he,?_⟩
  filter_upwards [small_span P,monitors G P.L,hE,h₅] with x hx ht hT hY
  intro c f S T hp hF hf F A V hA k i
  let p := Wisps.down S i
  rcases i with ⟨⟨o,i⟩,α⟩
  let j : Slots S := (o,i)
  let s' := temp x; let t := fiery G x P.L
  have ht' : 0 ≤ t := temp_nonneg _
  let L := fun z => pull o 0 (field V z)
  let W := L 0
  have hl : W=pull o 0 V := by unfold W L; rw [field_zero]
  let y : PriceCoords G c → _ := replica S.ratio ∘ L
  have hy (z : PriceCoords G c) : facade S o (field V z) 0 = y z := by rw [fixed_facade,← Identity.top_copy]; rfl
  suffices H : Point 0 p s n (fun z => Rows.restrict x (shots S x) A F (fixedBase T x (pulse x V z) k) j) (E*t) by
    exact H.color α
  unfold Rows.restrict; split
  swap
  · exact Point.zero (mul_nonneg he.le ht')
  next hi =>
    suffices H : Point 0 p s n (fun z => fixedBase T x (pulse x V z) k j) (max (M+U) (K+U')*t) by
      have hu := H.scale slip; rw [abs_of_pos slip_pos, ← mul_assoc] at hu; exact hu
    obtain ⟨hu,hv⟩ := h S V o
    obtain ⟨hs',hv',hw⟩ := ht
    let Q := Stores.till x
    obtain ⟨w,w',hK,hW⟩ := hF.feeds
    have haa (i : Site c) (h : secure x (radiusB x) i W) (j : Twin c) (hj : separation i j.1.1 ≤ Q) :
        Point 0 (o.act j.1.1) s n (fun z => T.Xn Q (L (s' • z)) j) (M'*t) := by
      unfold Xn; rw [hF.low]
      refine (h₂ L _ hu T.down w' hW s' t ht' hs'.le hv' hw Q _ S.patch.L.property j (fun l hh => ?_)).mono
        (le_trans (min_le_left a b) (min_le_right ..)) le_rfl
      rw [separation_signed] at hh
      apply le_trans _ hw
      apply h _
      have hz := separation_triangle i j.1.1 l.1; unfold Q Stores.till at *; omega
    rcases i with i|i
    · have hX : secure x (radiusB x) (S.ratio.parent i.1.1) W := by
        rw [hl]; exact Offset.guard V hA (.inl i.1) o (hp.symm ▸ hx) (F:=F) hi
      have hY : Point 0 p s n (fun z => T.Xf Q (facade S o (pulse x V z) 0) i) (M*t) := by
        simp_rw [pulse,hy,Xf,hF.high]; refine (h₁ y _ hv T.up w hK s' t ht' hs'.le hv' hw Q 1 (by decide) i
          (fun l he => ?_)).mono ((min_le_left a b).trans (min_le_left ..)) le_rfl
        dsimp only [Function.comp_apply] at he; rw [separation_signed] at he
        refine (hT S hp hf (S.ratio.parent i.1.1) W hX _ he).trans ?_
        exact (mul_le_mul_of_nonneg_left hw hD.le).trans_eq (by ring)
      have hN := h₃ S T hF (by rw [hp]) L (fun j z => T.Xn Q (L (s' • z)) j) _ hv Q s' t s ht' hs'.le hv' hs.le
        ((min_le_right a b).trans (min_le_left ..)) i (haa _ hX)
      apply (hY.sub hN).mono le_rfl
      rw [← add_mul]; exact mul_le_mul_of_nonneg_right (le_max_left ..) ht'
    have hX : secure x (radiusB x) i.1 W := by
      rw [hl]; exact Offset.guard V hA (.inr i) o (hp.symm ▸ hx) (F:=F) hi
    have hm := hY S hp hF.knobs hf F A V hA o i hi k hu
    have hI := h₄ S T hF L (fun j z => T.Xn Q (L (s' • z)) j) _ hu Q s' t s ht' hs'.le hv' hs.le
      ((min_le_right a b).trans (min_le_right ..)) i (haa _ hX)
    apply (hm.sub hI).mono le_rfl
    change K*t+U'*t ≤ _; rw [← add_mul]; exact mul_le_mul_of_nonneg_right (le_max_right ..) ht'
end YM.AnalyticBridge.SectorAffine.Offset
