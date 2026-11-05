import YM.Next.RANK.Helix
import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Continuation.Plane
import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Continuation.Psi


/-!
# Nonlinear chart bill on the same active Gaussian input

Not requiring tests throughout the torus, and not using a different Gaussian
to pay. Here nonlinear estimates only on *guarded* U. Physical Exp placements (in
the same order, including replica V, no coarsening of tag choices).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PhysicalGuard7f546.Curved
open Filter Function Lattice RG Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Rows Tree Bid Next.Rank.Spindle Next.Rank.Tapes
open Extra.Iteration Extra.Iteration.Scales UVNext.PricedKernels
open YM.AnalyticBridge.LocalGaussianLaws Current Lift Remote Local
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff MeasureTheory

variable {G : Gauge} {c f n : Side} {S : StepData c f}
    {F : Forest S.ratio} {x β : ℝ} {A : Stores S} {g : ℝ}
open FreeResolvent (treeInverse)

-- chart cost for the true order (including product error)
lemma twin_price (G : Gauge) : ∃ C D r : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ 0 < r ∧
    ∀ b : ℝ, b ≤ r → ∀ w v : G.Color, ‖w‖ ≤ b → ‖v‖ ≤ b →
    let u := G.lieExp w * G.lieExp v
    G.chord u ≤ C*b ∧ ‖G.curvature u - (w+v)‖ ≤ D*b^2 := by
  let X := fun a : G.Color => G.curvature (G.lieExp a)
  obtain ⟨D,r,hD,hr,H⟩ := chart_quadratic_cost X id
    (curvature_diff_mat G.lieExp (0:G.Color) G.exp_jet.contDiffAt).analyticAt (by
      intro a
      apply Work.F03.curvature_of_hasDerivAt
      have hd : HasFDerivAt (fun x => G.mat (G.lieExp x)) G.colorMat.toContinuousLinearMap
          ((0:ℝ) • a) := by rw [zero_smul]; exact G.expDiff_zero
      exact hd.comp_hasDerivAt 0 (show HasDerivAt (fun t : ℝ => t • a) a 0 by
        simpa using! (hasDerivAt_id' (0:ℝ)).smul_const a))
  obtain ⟨C,u,hC,hu,h⟩ := chord_chart_cost G
  have hx : 0 < G.colorScale := G.colorScale_pos
  refine ⟨2*C,G.colorScale*C^2+2*D,min u r,by positivity,by positivity,lt_min hu hr,?_⟩
  intro b hb w v hw hv y
  have he a (ha : ‖a‖≤b) : G.chord (G.lieExp a) ≤ C*b ∧ ‖X a-a‖ ≤ D*b^2 := by
    have hh := ((H a).2 (ha.trans (hb.trans (min_le_right ..))))
    rw [show X 0=0 by simp [X],zero_add] at hh
    exact ⟨(h a (ha.trans (hb.trans (min_le_left ..)))).trans (mul_le_mul_of_nonneg_left ha hC.le),
      hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ha _) hD.le)⟩
  obtain ⟨hk,hs⟩ := he w hw; obtain ⟨hB,hP⟩ := he v hv
  constructor
  · exact (G.chord_triangle ..).trans ((add_le_add hk hB).trans_eq (by ring))
  refine (norm_sub_le_norm_sub_add_norm_sub _ (X w+X v) _).trans ?_
  have Hr : ‖(X w+X v)-(w+v)‖ ≤ 2*D*b^2 := by
    rw [show X w+X v-(w+v)=(X w-w)+(X v-v) by abel]
    exact (norm_add_le ..).trans ((add_le_add hs hP).trans_eq (by ring))
  apply le_trans (add_le_add (weave (G.lieExp w) (G.lieExp v)) Hr)
  have hbp : 0 ≤ b := (norm_nonneg _).trans hw
  have ht := mul_le_mul_of_nonneg_left hk hx.le
  have hp := mul_le_mul ht hB (G.chord_nonneg _) (by positivity : 0 ≤ G.colorScale*(C*b))
  nlinarith only [hp]

private lemma wires (U : Config G f) (p : Cell f) {r d : ℝ} (v : Dir G f)
    (hr : ∀ e∈bones p, G.chord (U e) ≤ r) (hd : ∀ e∈bones p, ‖G.curvature (U e)-collect G v e‖ ≤ d) :
    let u := faceValue U p
    G.chord u ≤ 4*r ∧ ‖G.curvature u - Work.F03.faceCurl p v‖ ≤ 6*G.colorScale*r^2+4*d := by
  intro u
  let e : Bond f := (p.1,p.2.val.1);let i : Bond f := (p.1+step p.2.val.1,p.2.val.2)
  let j : Bond f := (p.1+step p.2.val.2,p.2.val.1);let k : Bond f := (p.1,p.2.val.2)
  have h₁ : G.chord (U e)≤r := hr _ (first_bone p)
  have h₂ : G.chord (U i)≤r := hr _ (second_bone p)
  have h₃ : G.chord (U j)≤r := hr _ (third_bone p)
  have h₄ : G.chord (U k)≤r := hr _ (last_bone p)
  rw [show u=U e*U i*(U j)⁻¹*(U k)⁻¹ from corners ..]; constructor
  · exact (G.chord_triangle ..).trans
      ((add_le_add ((G.chord_triangle ..).trans
        (add_le_add ((G.chord_triangle ..).trans (add_le_add h₁ h₂)) ((G.chord_inv _).trans_le h₃)))
        ((G.chord_inv _).trans_le h₄)).trans_eq (by ring))
  rw [curl_formula]
  let V a := G.curvature (U a);let W a := collect G v a
  refine (norm_sub_le_norm_sub_add_norm_sub _ (V e+V i-V j-V k) _).trans (add_le_add (warp4 h₁ h₂ h₃ h₄) ?_)
  change ‖(V e+V i-V j-V k)-(W e+W i-W j-W k)‖ ≤ _
  rw [show V e+V i-V j-V k-(W e+W i-W j-W k)=(V e-W e)+(V i-W i)-(V j-W j)-(V k-W k) by abel]
  exact (norm_sub_le ..).trans ((add_le_add ((norm_sub_le ..).trans (add_le_add
    ((norm_add_le ..).trans (add_le_add (hd _ (first_bone p)) (hd _ (second_bone p))))
    (hd _ (third_bone p)))) (hd _ (last_bone p))).trans_eq (by ring))

lemma joined_curl (P : Cell n) (v a : Dir G n) (g : ℝ) :
    Work.F03.faceCurl P (v+g • a) = Work.F03.faceCurl P v+g • Work.F03.faceCurl P a := by
  ext k
  change (Exterior.d 1 n *ᵥ (parts G 1 (v+g • a) k)) _ =
    ((Exterior.d 1 n *ᵥ (parts G 1 v k))+g • (Exterior.d 1 n *ᵥ (parts G 1 a k))) _
  have he : parts G 1 (v+g • a) k = parts G 1 v k+g • parts G 1 a k := rfl
  rw [he,mulVec_add,Matrix.mulVec_smul]

/-- Radius allowed for each active link, before multiplying by t/g. -/
def coolFraction : ℝ := 1/4096
lemma coolFraction_pos : 0<coolFraction := by unfold coolFraction; norm_num

lemma cooling (G : Gauge) (L : Side) : ∀ᶠ x in atTop, ∀ β : ℝ, x/2 ≤ β → β ≤ 3*x →
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S) (A : Stores S) (F : Forest S.ratio), ∀ W,
    let g:= coupling β; let e := accessing A F x W G; let l := loading A F x W G
    let t := fiery G x L
    ∀ v : Dir G c, ∀ (U : ℝ) (a Z : Gaussian.Vec (In x A F (G:=G))) (ε : ℝ),
    ∀ {Q : Gaussian.Table (In x A F (G:=G))} {J : Gaussian.Table (FreeResolvent.Active G F)},
    ε ≤ coolFraction → Guards W Z (ε*(t/g)) →
    ReadPrice Q J a (portrait_head T F v) g e l x U →
    ∀ i : Window A F x W, ‖g • tape (rebase T v a g W Z) i‖ ≤ 2 * coolFraction * t := by
  let K := (Fintype.card G.ColorIndex:ℝ); have hK : 0≤K := Nat.cast_nonneg _
  have ha := coolFraction_pos
  filter_upwards [eventually_ge_atTop 1, band G L, across G L,
    band_small G L (C:=coolFraction/(K+1)) (by positivity)] with x hx he hf hs
  intro β hB hh c f S T A F W g e l t v U a Z ε Q J hε hZ hp i
  obtain ⟨-, hg, -⟩ := he β hB hh; change 0<g at hg
  obtain ⟨-, -, hT, -⟩ := hf; change 0<t at hT
  let b := portrait_head T F v
  let δ := displacement a b g e l
  have h : ‖tape δ i‖ ≤ K := by
    have hk c : |tape δ i c| ≤ x^(-(1/8):ℝ) := hp.paid.shift_size (i,c)
    refine (color_count zero_le_one _ (fun c => (hk c).trans
      (Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)))).trans_eq (mul_one _)
  have hG : g*K ≤ coolFraction*t := by
    have ht := hs β hB hh
    change g≤coolFraction/(K+1)*t at ht
    apply le_trans (mul_le_mul_of_nonneg_left (show K≤K+1 by linarith) hg.le)
    exact (mul_le_mul_of_nonneg_right ht (show 0 ≤ K+1 by positivity)).trans_eq (by field_simp)
  rw [norm_smul,Real.norm_of_nonneg hg.le,show tape (rebase T v a g W Z) i=tape δ i+tape Z i.val from rfl]
  refine (mul_le_mul_of_nonneg_left ((norm_add_le ..).trans (add_le_add h (hZ i))) hg.le).trans ?_
  rw [mul_add]; have ht : g*(ε*(t/g))≤coolFraction*t := by
    exact Eq.trans_le (show g*(ε*(t/g))=ε*t by field_simp) (mul_le_mul_of_nonneg_right hε hT.le)
  linarith only [ht,hG]

lemma link_pricing (G : Gauge) (P : Patch) (Pt : Teller G) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ᶠ x in atTop,
    ∀ β : ℝ, x/2 ≤ β → β ≤ 3*x →
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T →
    ∀ o : Site c, ∀ A : Stores S, Clears A x o (radiusB x) →
    ∀ v : Dir G c, ‖v‖ ≤ linkRoom x → ∀ V : Config G c, AgreeNear id o (radiusB x) V (represent v) →
    ∀ (F : Forest S.ratio) (a Z : Gaussian.Vec (In x A F (G:=G))) (Y : LinkArray G (Frozen A x F)),
    ∀ W, Reachable S o x W →
    let g:=coupling β; let z := vertical S (plantW S (rebase T v a g W Z)); let u:=physical A F V Y (tape (a+g • Z))
    let t:=fiery G x P.L; let h:=linkRoom x
    ∀ {J : Gaussian.Table (FreeResolvent.Active G F)} {Q : Gaussian.Table (In x A F (G:=G))}
      (U ε : ℝ), ε ≤ coolFraction → Guards W Z (ε*(t/g)) →
    ReadPrice Q J a (portrait_head T F v) g (accessing A F x W G) (loading A F x W G) x U →
    ∀ i∈W, ‖g • collect G z i‖ ≤ 2*coolFraction*t ∧ G.chord (u i) ≤ C*h ∧
      ‖G.curvature (u i)-collect G (low T F v+g • z) i‖ ≤ D*h^2 := by
  obtain ⟨K,hK,h⟩ := carry_summary G P Pt.bind Pt
  obtain ⟨C,D,r,hC,hD,hr,hk⟩ := twin_price G
  let L:=K+1; have hL : 1≤L := by unfold L; linarith
  have hl : Tendsto (fun x => L*linkRoom x) atTop (𝓝 0) := by simpa using linkRoom_tends.const_mul L
  refine ⟨C*L,D*L^2,mul_nonneg hC (zero_le_one.trans hL),by positivity,?_⟩
  filter_upwards [eventually_gt_atTop 0,band G P.L,across G P.L,cooling G P.L,threshold_small G P.L,
    hl.eventually (ge_mem_nhds hr)] with x hx hb hh hy ht hD'
  intro β hi hi' c f S T hP hT o A hA v hv V hV F a Z Y W hW g z u t R J Q U ε hε hZ hp i hu
  have h0 : 0<g := (hb β hi hi').2.1
  have hr' : 0 < R := linkRoom_pos hx
  have hf : ‖g • collect G z i‖ ≤ 2*coolFraction*t := by
    by_cases hF : i∈F.trunks
    · rw [on_tree _ _ hF,smul_zero,norm_zero]; have hv : 0 < t := hh.2.2.1; have := coolFraction_pos; positivity
    let j : F.Free := ⟨i,hF⟩
    let e : Active A x F := ⟨j,live_test A F hA j ((hW _ hu).trans (by omega))⟩
    let k : Window A F x W := ⟨e,hu⟩
    let ζ:=rebase T v a g W Z
    rw [show collect G z i=tape ζ k from plant_on _ k]
    exact hy β hi hi' S T A F W v U a Z ε hε hZ hp k
  let w := doc T F v i+g • collect G z i
  let q := collect G (blueprint S v) i
  have H1 : ‖doc T F v i‖ ≤ K*R := (norm_le_pi_norm ..).trans ((h S T hP hT.knobs hT F v).trans
    (mul_le_mul_of_nonneg_left hv hK))
  have hw : ‖w‖ ≤ L*R := by
    apply (norm_add_le ..).trans ((add_le_add H1 hf).trans ?_)
    have he : t ≤ R := ht
    unfold coolFraction L; linarith
  have hq : ‖q‖ ≤ L*R := (norm_le_pi_norm (blueprint S v) (i.1,coord i.2)).trans
    (((blueprint_bill v).trans hv).trans (le_mul_of_one_le_left hr'.le hL))
  have hz : u i=G.lieExp w * G.lieExp q := link_frame T v a Z Y V hV hA hW h0.ne' i hu
  have HE : w+q=collect G (low T F v+g • z) i := by
    unfold w q doc collect
    simp only [Pi.smul_apply,Pi.add_apply,Pi.sub_apply]; abel
  rw [hz,← HE]
  obtain ⟨h1,h2⟩ := hk (L*R) hD' _ _ hw hq
  exact ⟨hf,h1.trans_eq (by ring),h2.trans_eq (by ring)⟩

/-- Use this with the r.h.s. scaled mean `flow` (same g); it retains
*actual* palette and portrait with frozen Haar/tags. -/
structure Central {o : Site c} (v : Dir G c) (V : Config G c) (T : Tube G S) (H L : Bed)
    (a Z : Gaussian.Vec (In x A F (G:=G))) (Y : LinkArray G (Frozen A x F))
    (X : Support f) (W : Finset (Bond f)) (g t : ℝ) (l : ℕ) : Prop where
  readyAt : Reachable S o x W
  covers : Covers X W
  slack (p : Cell f) : (∃ y∈X,y∈touched p) →
    G.chord (faceValue (physical A F V Y (tape (a+g • Z))) p) < t/8
  prediction (i : Occasion G f) : i.place ⊆ X → i.link.length ≤ stride l x →
    let z := sectionCurl (rebase T v a g W Z)
    let u := physical A F V Y (tape (a+g • Z)); let b := i.link.atSite u i.location
    let k := flow S H L T (look V) i.coordFace
    ‖k‖ ≤ t/4096 ∧ ‖b‖ ≤ t ∧ ‖g⁻¹ • b - (g⁻¹ • k + z i.coordFace)‖ ≤ x^(-(1/8):ℝ)

lemma Central.heat {T H L V v a Z t o l W} (X : Support f) (ht : 0 ≤ t)
    (Y : LinkArray G (Frozen A x F)) (h : Central (o:=o) v V T H L a Z Y X W g t l) :
    Healthy t X (physical A F V Y (tape (a+g • Z))) := by
  apply Finset.disjoint_left.mpr
  intro i hi he; obtain ⟨p,hp,hk⟩ := (flags_spec ..).mp he
  have hh := h.slack p ⟨i,hi,hp⟩
  linarith only [hh,hk,ht]

set_option maxHeartbeats 600000 in
theorem interior_price (G : Gauge) (P : Patch) (Pt : Teller G) {s a b : ℝ} (hs : 0 < s)
    (hr : s ≤ Pt.η) (hA : 0 ≤ a) (hB : 0 ≤ b) (he : 0 ≤ Pt.C) (hL : Spacing G P.L s Pt.C a b) (l : ℕ) :
    ∀ᶠ x in atTop,
    ∀ β : ℝ, x/2 ≤ β → β ≤ 3*x →
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T → ∀ H L : Bed,
    ∀ u V : ℝ, Floor H T.high f u V → Towers.Diagonal S H L T.R → H.covered s a → L.covered s b →
    ∀ o : Site c, ∀ (A : Stores S), Clears A x o (radiusB x) →
    ∀ v : Dir G c, ‖v‖ ≤ linkRoom x → ∀ V : Config G c, A.flags=RG.flags (temp x) V →
    AgreeNear id o (radiusB x) V (represent v) →
    ∀ (F : Forest S.ratio) (a Z : Gaussian.Vec (In x A F (G:=G))) (Y : LinkArray G (Frozen A x F)),
    ∀ X W, Reachable S o x W → Covers X W →
    let g:=coupling β; let t:=fiery G x P.L
    ∀ {Q : Gaussian.Table (In x A F (G:=G))} (U ε : ℝ), ε ≤ coolFraction → Guards W Z (ε*(t/g)) →
    ReadPrice Q (treeInverse G S F H.metric 0) a (portrait_head T F v) g
      (accessing A F x W G) (loading A F x W G) x U →
    Central (o:=o) v V T H L a Z Y X W g t l := by
  obtain ⟨C,hC,HK⟩ := curl_budget G P Pt hs hr hA hB he hL
  obtain ⟨D,E,hD,hE,H⟩ := link_pricing G P Pt
  obtain ⟨K,r,-,hr',hl⟩ := Work.E05.curvature_lower G
  let F₀ := 6*G.colorScale * D^2 + 4*E
  let F₁ := 8*G.colorScale * D^2
  have hv := G.colorScale_pos
  have hF0 : 0 ≤ F₀ := by unfold F₀; positivity
  have hF1 : 0 ≤ F₁ := by unfold F₁; positivity
  have H' : Tendsto (fun x => (4*D)*linkRoom x) atTop (𝓝 0) := by simpa using linkRoom_tends.const_mul (4*D)
  filter_upwards [H,HK,across G P.L,band G P.L, threshold_large G P.L (1024*F₀) (by positivity),
    H'.eventually (ge_mem_nhds hr'), band_price G P.L (F₀+C+F₁) (by positivity) l] with
      x hx hi hα hβ hbig ht hprice
  obtain ⟨hX,-,hT,-⟩ := hα
  intro β hβ0 hβ1 c f S T hS hT' B L u V hB' hT0 hf hb o A hA' v hv0 V0 hU hU' F a Z Y X W hw hW g t Q U ε hε hZ hp
  let U' := physical A F V0 Y (tape (a+g • Z))
  let z := vertical S (plantW S (rebase T v a g W Z)); let b := low T F v; let R:=linkRoom x
  have hY : 0<R := linkRoom_pos hX
  have hj : 0<g := (hβ _ hβ0 hβ1).2.1
  change 0<t at hT
  have hs := hx β hβ0 hβ1 S T hS hT' o A hA' v hv0 V0 hU' F a Z Y W hw U ε hε hZ hp
  have hd (p : Cell f) (hh : bones p ⊆ W) :
      let i : Body 2 f := (p.1,plaquette p.2)
      let m := flow S B L T (look V0) i
      let y := sectionCurl (rebase T v a g W Z) i
      ‖m‖ ≤ t/4096 ∧
        G.chord (faceValue U' p) ≤ 4*(D*R) ∧ G.chord (faceValue U' p) < t/8 ∧
        ‖G.curvature (faceValue U' p) - (m+g • y)‖ ≤ (F₀+C)*R^2 := by
    intro i m y
    have H := first_bone p
    obtain ⟨he,hP,hQ⟩ := hi S T hS hT' B L u V hB' hT0 hf hb o A hA' V0 hU v hU' hv0 F i (hw _ (hh H))
    let B' := Work.F03.faceCurl p b
    let z' := g • y
    change ‖B' - m‖ ≤ C*R^2 at he
    change ‖m‖ ≤ t/4096 at hP
    change ‖B'‖ ≤ t/2048 at hQ
    have hp : ‖z'‖ ≤ 4*(2*coolFraction*t) := by
      have hv := curl_price (v:=g • z) p (r:=2*coolFraction*t) (fun i he => (hs i (hh he)).1)
      have ht : z'=Work.F03.faceCurl p (g • z) := by
        unfold z'
        ext k
        have h : parts G 1 (g • z) k=g • parts G 1 z k := rfl
        change (g • Exterior.d 1 f *ᵥ parts G 1 z k) _ = (Exterior.d 1 f *ᵥ parts G 1 (g • z) k) _
        rw [h,Matrix.mulVec_smul]
      exact ht.symm ▸ hv
    obtain ⟨h₁,h₂⟩ := wires U' p (r:=D*R) (d:=E*R^2) (b+g • z)
      (fun i hv => (hs i (hh hv)).2.1) (fun i hv => (hs i (hh hv)).2.2)
    rw [joined_curl] at h₂
    change ‖G.curvature (faceValue U' p) - (B'+z')‖ ≤ _ at h₂
    have h₂ : ‖G.curvature (faceValue U' p) - (B'+z')‖ ≤ F₀*R^2 :=
      h₂.trans_eq (by unfold F₀; ring)
    refine ⟨hP,h₁,?_,?_⟩
    · have hq := (norm_le_norm_sub_add (G.curvature (faceValue U' p)) (B'+z')).trans
        (add_le_add h₂ ((norm_add_le ..).trans (add_le_add hQ hp)))
      have hk : ‖G.curvature (faceValue U' p)‖ ≤ t/32 := by
        apply hq.trans
        change 1024*F₀*R^2≤t at hbig
        unfold coolFraction; linarith only [hbig,hT]
      let w := faceValue U' p
      have h : G.chord w ≤ r := h₁.trans (Eq.trans_le (show 4*(D*R)=(4*D)*R by ring) ht)
      have hh := (hl w h).2
      change G.chord w < t/8; change ‖G.curvature w‖≤t/32 at hk
      nlinarith only [hh,pow_le_pow_left₀ (norm_nonneg (G.curvature w)) hk 2,hT]
    refine (norm_sub_le_norm_sub_add_norm_sub _ (B'+z') (m+z')).trans
      ((add_le_add h₂ ?_).trans_eq (add_mul ..).symm)
    rwa [add_sub_add_right_eq_sub]
  refine ⟨hw,hW,fun p hh => (hd p (hW.flags p hh)).2.2.1,?_⟩
  intro i hh hj' y U1 B' m
  let R' := stride l x; let p := i.face; let w := i.location; let v := i.link.walk
  obtain ⟨hM,hf,hμ,hσ⟩ := hd p (hW.flags _ ⟨p.1,hh i.face_mem,Work.E01.base_touched _⟩)
  have hN : (v.length:ℝ) ≤ R' := by
    exact_mod_cast (show v.length ≤ R' from le_trans (by unfold v Slot.length; omega) hj')
  have hChord : G.chord (travel U' w v) ≤ (R':ℝ)*(D*R) := by
    have he : travel U' w v=travel (expandAt w U') 0 v := by rw [travel_at,map_zero,zero_add]
    rw [he]
    refine (impulse (j:=v) 0 (mul_nonneg hD hY.le) (fun e he ht =>
      (hs _ (hW.from_start i hh e he)).2.1)).trans (mul_le_mul_of_nonneg_right hN (mul_nonneg hD hY.le))
  rw [show B'=G.adjoint (travel U' w v) (G.curvature (faceValue U' p)) from Work.F03.atSite_path ..]
  refine ⟨hM, ?_, ?_⟩
  · rw [G.norm_adjoint]; exact (G.curvature_norm _).trans (hμ.le.trans (by linarith))
  let k:=G.curvature (faceValue U' p); let Z':= y i.coordFace; let B₀:=G.adjoint (travel U' w v) k
  have h0 : ‖B₀-k‖ ≤ F₁ * R' * R^2 := by
    apply (adjoint_norm_sub ..).trans
    apply le_trans (mul_le_mul (mul_le_mul_of_nonneg_left hChord (by positivity)) ((G.curvature_norm _).trans hf)
      (norm_nonneg _) (by positivity)); exact le_of_eq (by unfold F₁; ring)
  change ‖g⁻¹ • B₀-(g⁻¹ • m+Z')‖ ≤ _
  rw [show g⁻¹ • B₀-(g⁻¹ • m+Z')=g⁻¹ • (B₀-(m+g • Z')) by
    rw [smul_sub,smul_add,smul_smul,inv_mul_cancel₀ hj.ne',one_smul],norm_smul,
    Real.norm_of_nonneg (inv_pos.mpr hj).le,← div_eq_inv_mul]
  apply le_trans (div_le_div_of_nonneg_right ((norm_sub_le_norm_sub_add_norm_sub _ k _).trans
    (add_le_add h0 hσ)) hj.le) (le_trans ?_ (hprice β hβ0 hβ1))
  apply div_le_div_of_nonneg_right _ hj.le
  have hh : 1 ≤ (R':ℝ) := by exact_mod_cast stride_ge l x
  refine le_trans (add_le_add_right (show (F₀+C)*R^2 ≤ (F₀+C)*(R':ℝ)*R^2 from
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hh) (sq_nonneg _)) _) (le_of_eq ?_)
  change _ = (F₀+C+F₁)*R'*R^2; ring
end YM.PhysicalNext.PhysicalGuard7f546.Curved
