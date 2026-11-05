import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.LocalStation

/-!
# Cost of actual base→ideal base at estimated locations

Fixed V after gauge $z$. Remote only: `firstTerm` on global extension
in the same gauge. Reads tested on inner patch of cleared radius. Error
in one row before D^T; retain fixed-order p/global radius and true-cut
exp using all of registry kernel data `Pt,Tube` for that actual step.
Included both face and bond directions, not un-swapping noise legs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Lift
open Function Filter Lattice RG Wilson Finset Pressure Pressure.Stores Pressure.Tube Precision Exterior Tree Bloch Bid Matrix
open Next Next.Fluctuations SectorChange SectorChange.Rows SectorChange.Gaussian Push.SectorMeasure  Remote
open scoped Topology InnerProductSpace BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

-- from Kernel/Global results; zip costs no clipping after stamp
lemma v_cost {X Y : Type} [Fintype X] [Fintype Y] {F H : X → Y → Pay G} {C k : ℝ} (hK : NearFlat F H C k)
    (v b : Y→G.Color) {W Z : ℝ} (h : 0≤W) (he : 0≤Z) (hv : ∀ y, ‖v y‖ ≤ W) (ht : ∀ y, ‖b y - v y‖ ≤ Z) (i : X) :
    ‖zip F b i-zip H v i‖ ≤ C*k*W+C*Z := by
  have hh : zip F b i-zip H v i=zip (F-H) v i+zip F (b-v) i := by unfold zip; simp only [Pi.sub_apply, _root_.sub_apply, sum_sub_distrib,map_sub]; abel
  rw [hh]
  exact (norm_add_le ..).trans (add_le_add (Work.E07.zip_uniform _ _ _ (hK.close.rows i) h hv) (Work.E07.zip_uniform F _ _ (hK.cut.rows i) he ht))

lemma base_summary (Pt : Teller G) (P : Patch) (h : P.Branches Pt.bind G) :
    ∃ C δ τ : ℝ, 0≤C ∧ 0<δ ∧ 0<τ ∧ ∀ᶠ x in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T →
    ∀ (U : Stores S) (o : Site c), Clears U x o (radiusB x) → ∀ (V : Config G c) (v : Dir G c) (t : ℝ),
    U.flags = RG.flags (temp x) V → AgreeNear id o (radiusB x) V (represent v) → ‖v‖ ≤ t → t ≤ δ →
    ∀ (k : S.Choices) (s : Signed) (j : Twin f ⊕ Bond c), separation o (Remote.aim S (s,j)) ≤ radiusB x/2 →
      ‖Rows.base T x V k (s,j)-firstTerm T v (s,j)‖ ≤ C*t*widen (till x) t τ := by
  obtain ⟨C₁,r₁,h1,h1r,hf⟩ := x_chart_cost G Pt.top 1 (by decide)
  obtain ⟨C₂,r₂,h2,h2r,hg⟩ := x_chart_cost G Pt.below P.L.val P.L.property
  obtain ⟨C₃,r₃,h3,h3r,hz⟩ := z_chart_cost P Pt.bind G h
  obtain ⟨C₄,τ,r₄,h4,hτ,h4r,hK⟩ := kernel_chart_cost G P.L Pt.η Pt.C Pt.width
  let δ:= min (min r₁ r₂) (min r₃ r₄)
  let L:ℝ := P.L.val; let Y:=min τ (min Pt.top.width (Pt.below.width/L))
  have hL : 0<L := by unfold L; exact_mod_cast P.L.pos
  have hY : 0<Y := lt_min hτ (lt_min Pt.top.width_pos (div_pos Pt.below.width_pos hL))
  let N := C₁+C₂+C₃+C₄; let M:=N+2*N^2
  have hN : 0≤N := by unfold N; positivity
  have hc1 : C₁≤N := by unfold N; linarith
  have hc2 : C₂≤N := by unfold N; linarith
  have hc3 : C₃≤N := by unfold N; linarith
  have hc4 : C₄≤N := by unfold N; linarith
  refine ⟨M,δ,Y,by unfold M; positivity,lt_min (lt_min h1r h2r) (lt_min h3r h4r),hY,?_⟩
  filter_upwards [stamped (G:=G) Pt.below.clip, small_span P] with x hx hB
  intro c f S T hP ht U o hh V v t hw hv ha hu k s j hp
  let a := pulled (blueprint S v) s; let b:=pulled v s
  have he : S.patch.Branches S.kernel G := by rw [hP,ht.knobs]; exact h
  rw [hx S U o hh V T k ht.low he hw (hP ▸ hB) s v j hv hp]
  have hs : 0≤t := (norm_nonneg _).trans ha
  have hA : ‖a‖ ≤ t := (swapped ..).trans ((blueprint_bill ..).trans ha)
  have hD : ‖b‖ ≤ t := (swapped ..).trans ha
  let R:=till x; let D:=widen R t Y
  let y:=represent a; let z:=represent b
  obtain ⟨Λ,Λ',hΛ,hΛ'⟩ := ht.feeds
  have hZ : 0≤D := widen_nonneg _ hs
  have hL' : S.patch.L=P.L := by rw [hP]
  obtain ⟨hQ,hW,-⟩ := hK S T hL' ⟨_,ht.crosses⟩ R b t hD (hu.trans ((min_le_right ..).trans (min_le_right ..)))
  let β := widen R t τ
  have hm : β≤D := widen_anti R t (min_le_left ..)
  have hβ : 0≤β := widen_nonneg _ hs
  let f_cost : ∀ i, ‖xLin T.high T.up a i‖ ≤ N*t ∧ ‖T.Xf R y i-xLin T.high T.up a i‖ ≤ N*t*D := fun i => by
    have H:= hf f T.up Λ hΛ R a t hA (hu.trans ((min_le_left ..).trans (min_le_left ..))) i
    rw [Nat.cast_one,div_one] at H
    unfold Tube.Xf; rw [ht.high]; exact ⟨H.1.trans (by gcongr), H.2.trans (mul_le_mul (by gcongr) (widen_anti R t ((min_le_right ..).trans (min_le_left ..))) (widen_nonneg _ hs) (mul_nonneg hN hs))⟩
  let V0:=T.Xn R z; let V':=xLin T.low T.down b
  have v_cost' : ∀ i, ‖V' i‖ ≤ N*t ∧ ‖V0 i-V' i‖ ≤ N*t*D := fun i=> by
    have H:= hg c T.down Λ' hΛ' R b t hD (hu.trans ((min_le_left ..).trans (min_le_right ..))) i
    unfold V0 V' Tube.Xn; rw [ht.low,hL']; exact ⟨H.1.trans (by gcongr),H.2.trans (mul_le_mul (by gcongr) (widen_anti R t ((min_le_right ..).trans (min_le_right ..))) (widen_nonneg _ hs) (mul_nonneg hN hs))⟩
  have zip_it {I : Type} [Fintype I] (F H : I→Twin c→Pay G) (h : NearFlat F H C₄ β) :
      ∀ i, ‖zip F V0 i - zip H V' i‖ ≤ 2*N^2*t*D := fun i => by
    have he := v_cost (G:=G) (W:=N*t) (Z:=N*t*D) h V' V0 (mul_nonneg hN hs) (by positivity) (fun i => (v_cost' i).1) (fun i => (v_cost' i).2) i
    refine he.trans ?_
    calc
      _ ≤ N*D*(N*t)+N*(N*t*D) := by gcongr
      _ = _ := by ring
  have bond_it (i : Bond c) : ‖Z S (S.prediction y (Oriented.choice s k)) z i - zLin S a b i‖ ≤ N*t*D := by
    have hh := (hz c f S hP ht.knobs (Oriented.choice s k) i (a,b)).2 (by apply le_trans (max_le hA hD) (hu.trans ((min_le_right ..).trans (min_le_left ..))))
    apply hh.trans
    rw [sq,← mul_assoc]; have he : ‖(a,b)‖ ≤ t := max_le hA hD
    have hg : ‖(a,b)‖ ≤ D := he.trans (le_widen R hs)
    gcongr
  have heal (x y z w : G.Color) (he : ‖x-y‖ ≤ N*t*D) (hf : ‖z-w‖ ≤ 2*N^2*t*D) :
      ‖(x-z)-(y-w)‖ ≤ M*t*D := by rw [show x-z-(y-w)=x-y-(z-w) by abel]; exact (norm_sub_le ..).trans ((add_le_add he hf).trans_eq (by unfold M; ring))
  cases j
  next j => exact heal (T.Xf R _ j) _ (zip _ _ j) (zip (flatF T) _ j) (f_cost j).2 (zip_it _ _ hQ j)
  next j => exact heal _ _ _ _ (bond_it j) (zip_it _ _ hW j)
end YM.AnalyticBridge.LocalGaussianLaws.Lift
