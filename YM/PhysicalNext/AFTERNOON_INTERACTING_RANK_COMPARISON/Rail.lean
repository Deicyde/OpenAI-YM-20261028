import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Focusing
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Illumined

/-!
# Calculating on V-photo arguments link by link

At the issued kernel and field, this pre-estimate uses *one θ*. Centered
z-view on actual gauge+flag choice, literally for *all* choices as typed.
Keep walls = M² of restarted threshold, x-dependent receipts.
Primitive unmarked energy steps not inferred.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Paint Spindle WeightedGaussianMarginal45C.Issue.Cut UVNext.PricedKernels
    YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory
    AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian FreeResolvent Wisps
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}
    {x β g d : ℝ} {A : Stores S} {F : Forest S.ratio}

section era

-- One natural ambient choice: use all active links, zero-pad away.
def breadth (Z : Gaussian.Vec (In x A F (G:=G))) : Dir G f :=
    vertical S (F:=F) (insertion (loadLink A F x (G:=G)) *ᵥ Z)
lemma breathes (Z : Gaussian.Vec (In x A F (G:=G))) (i) : collect G (breadth Z) i.val.val = tape Z i := by
  unfold breadth Curved.vertical; rw [Work.F01.collect_vertical, dif_neg i.val.property]
  ext j
  exact insertion_at _ Z (Function.Embedding.injective (loadLink A F x)) (i,j)
lemma rainShift (Z : Gaussian.Vec (In x A F (G:=G))) : dKeys A F x *ᵥ Z =
    flatten (dColor G f 1 (breadth Z)) := by
  rw [show flatten (dColor G f 1 (breadth Z)) = plane S F *ᵥ (insertion (loadLink A F x) *ᵥ Z) from authentic (insertion (loadLink A F x) *ᵥ Z),Matrix.mulVec_mulVec]; unfold dKeys
  congr! 1
  ext i j; rw [Matrix.mul_apply]; simp [insertion,mul_ite]

variable {o : Site c} {W w : ℕ} (k : S.Choices) (q : Chi) (T : Tube G S) {U : ℝ} {V : Config G c} {v : Dir G c}
variable {Pt : Teller G}
lemma slide_link (hV : Pose A o W x V v) (F : Forest S.ratio) (Y : RoomView A (retime x) F G)
    (h : Pt.Funds S T) (hp : Enlightened S.patch Pt w x β) (hm : ∀ j, separation o (front A F j)+walls x ≤ W → |portrait T A F k (retime x) (spine V o) .endpoint q d Y.1 j - portrait_head T F v (loadLink A F (retime x) j)|≤x^(-(7/8):ℝ))
    (j : Bond f) (hj : separation o (S.ratio.parent j.1)+walls x≤W) {X : Finset (Bond f)} (hi : j∈X) (hG : Guards X Y.2 (haze G x β S.patch.L)) :
    let v' := spine V o; let U := gazed T k q v' (retime x) β d Y; let l:= low T F v
    let g:=coupling β; let z:=breadth Y.2
    ‖g • collect G z j‖ ≤ coolFraction*phase (betaF G x S.patch.L) ∧
    G.chord (U j) ≤ highPrice G * linkRoom x ∧
    ‖G.curvature (U j)-collect G (l+g • z) j‖ ≤ edgeFire G x := by
  intro v' U l g z
  let i:= j.1; let m := S.ratio.parent i; let b := blueprint S v
  obtain ⟨h1,h2,h3⟩:= hV.center m hj
  have ht : replica S.ratio v' j= G.lieExp (collect G b j) := by
    rw [copyAgree v' _ m _ h2 j (by unfold m i; simp),replica_rep v]
    simp only [represent,increment,Pi.one_apply,mul_one,b]
  let e:= linkRoom x; let a:= coolFraction; let t:=phase (betaF G x S.patch.L); let M:=(Fintype.card G.ColorIndex:ℝ)
  have hg : 0<g:=coupling_pos hp.sparks
  have hp' := hp.plus e rfl
  have hv' : ‖v‖≤clearanceFare (retime x) := by linarith only [hV.worth,norm_nonneg v]
  have hv : ‖collect G b j‖ ≤ e := (norm_le_pi_norm b (j.1,coord j.2)).trans ((blueprint_bill v).trans (hv'.trans hp'.1))
  have hz : 0<e:= linkRoom_pos hp.stable; have hC : 0<t:= alpha_phase _ (add_pos_of_pos_of_nonneg hp.stable (Work.E04.shift_nonneg G S.patch.L))
  have ha : 0<a:=coolFraction_pos
  obtain ⟨hH,hA,ht',hK⟩:= (twin_price G).choose_spec.choose_spec.choose_spec
  let L:=doc T F v; let R:=g • collect G z j
  have HE (w : G.Color) (hj : U j= G.lieExp w*replica S.ratio v' j) (hk : ‖w‖≤e) (hy : ‖w-(L j + R)‖ ≤ M*e^2) :
      G.chord (U j) ≤ highPrice G * e ∧ ‖G.curvature (U j)-collect G (l+g • z) j‖ ≤ edgeFire G x := by
    rw [hj,ht]
    obtain ⟨h1,h2⟩ := hK e hp'.2.1 w _ hk hv
    refine ⟨h1,(norm_sub_le_norm_sub_add_norm_sub _ (w+collect G b j) _).trans (le_trans (add_le_add (d:=M*e^2) h2 ?_) ?_)⟩
    swap
    · change arcPrice G*e^2 + M*e^2 ≤ _; exact (add_mul ..).symm.le
    rwa [show w+collect G b j - collect G (l+g • z) j=w-(L j + R) from by unfold l L R b doc collect; simp only [Pi.sub_apply,Pi.smul_apply,Pi.add_apply]; abel]
  by_cases H : j∈F.trunks
  · have he : R=0:= by unfold R; rw [show collect G z j=0 from on_tree (S:=S) (F:=F) _ j H,smul_zero]
    constructor
    · change ‖R‖≤a*t; rw [he,norm_zero]; positivity
    refine HE 0 ?_ ?_ ?_
    · rw [show U j=1 from F.on_tree _ ⟨j,H⟩,G.mat_lieExp_zero]; rw [show replica S.ratio v' j=1 from if_pos (F.trunk_internal (by exact H))]; rw [mul_one]
    · rw [norm_zero]; exact hz.le
    rw [he,show L j = 0 from doc_trunk T F v j H]; simp only [add_zero,sub_zero,norm_zero]; unfold M; positivity
  let i : F.Free:=⟨j,H⟩; let a0 : Active A (retime x) F:=⟨i,live_test A F h1 i (by change separation m m≤_; simp)⟩
  let H:=portrait T A F k (retime x) v' .endpoint q d Y.1
  let w:= tape H a0; have He : tape (H + g • Y.2) a0 = w + R := by
    unfold R; rw [show collect G z j=tape Y.2 a0 from breathes Y.2 a0]; rfl
  have hU : U j = G.lieExp (w+R)*replica S.ratio v' j := by
    rw [← He]; exact (F.off_tree _ i).trans (freeze_regular (j:=a0) ..)
  have hr : ‖R‖ ≤ a*t := by
    unfold R; rw [show collect G z j=tape Y.2 a0 from breathes Y.2 a0,norm_smul,Real.norm_of_nonneg hg.le]
    exact (mul_le_mul_of_nonneg_left (hG ⟨a0,hi⟩) hg.le).trans_eq (by change g*(a*(t/g))=_; field_simp)
  let r := x^(-(7/8):ℝ)
  have hx : ‖w - L j‖ ≤ M*r := color_count (Real.rpow_nonneg hp.stable.le _) _ (fun k => hm (a0,k) hj)
  have he' := hp.books S T rfl h F v hv'
  refine ⟨hr,HE _ hU ?_ (by rw [add_sub_add_right_eq_sub]; exact hx.trans (mul_le_mul_of_nonneg_left hp'.2.2 (Nat.cast_nonneg _)))⟩
  refine (norm_add_le ..).trans (le_trans (add_le_add ((norm_le_norm_sub_add w (L j)).trans (add_le_add hx (norm_le_pi_norm L _))) hr) ?_); linarith only [he']
end era


-- Four-bond product and support checks separate from getting the μ by an Atlas application.
private lemma checkingMask (P : Finset (Bond f)) (E : Config G f) (u : Cell f) (hR : bones u⊆P)
    (V : Patch) (U : Teller G) {w : ℕ} (he : Enlightened V U w x β) (l z : Dir G f) (g t e : ℝ) (ht : 0<t)
    (hhT : t=phase (betaF G x V.L)) (hD : e=edgeFire G x)
    (hr : ∀ i∈P, ‖g • collect G z i‖ ≤ coolFraction*t ∧ G.chord (E i) ≤ highPrice G*linkRoom x ∧
      ‖G.curvature (E i)-collect G (l+g • z) i‖ ≤ e) (h : ‖Work.F03.faceCurl u l‖ ≤ t/2048) :
    G.chord (faceValue E u) ≤ t/8 := by
    subst e; subst t
    let t:=phase (betaF G x V.L); let e:=edgeFire G x; let a:=coolFraction
    let A' := l + g • z
    obtain b:= hr _ (hR (first_bone _)); obtain c:=hr _ (hR (second_bone _))
    obtain u':=hr _ (hR (third_bone _)); obtain d':=hr _ (hR (last_bone _))
    obtain ⟨_,_,hu⟩ := (Work.E05.curvature_lower G).choose_spec.choose_spec
    let ξ:=faceValue E u; let P0:= Work.F03.faceCurl u A'
    have hs : G.chord ξ ≤ lampRadius G := by
      unfold ξ; rw [corners]; apply le_trans _ he.low
      exact (G.chord_triangle ..).trans ((add_le_add ((G.chord_triangle ..).trans (add_le_add ((G.chord_triangle ..).trans
        (add_le_add b.2.1 c.2.1)) ((G.chord_inv _).trans_le u'.2.1))) ((G.chord_inv _).trans_le d'.2.1)).trans_eq (by ring))
    have hj : ‖g • Work.F03.faceCurl u z‖ ≤ 4*(a*t) := by
      rw [show g • Work.F03.faceCurl u z = Work.F03.faceCurl u (g • z) by
        rw [curl_formula,curl_formula]; simp only [collect, Pi.smul_apply,smul_sub,smul_add]]
      exact curl_price _ u (fun i hi=> (hr i (hR hi)).1)
    have hZ : ‖P0‖ ≤ t/2048+ 4*(a*t) := by
      unfold P0 A'; rw [joined_curl]; exact (norm_add_le ..).trans (add_le_add h hj)
    have hξ := (hu ξ hs).2
    have hX : ‖G.curvature ξ - P0‖ ≤ t/64 := by
      unfold P0; rw [curl_formula]; unfold ξ; rw [corners]
      have hL:=warp4 b.2.1 c.2.1 u'.2.1 d'.2.1
      let P' := fun i=>G.curvature (E i); let R:= P' - collect G A'
      -- precise vector error then mean
      apply (norm_sub_le_norm_sub_add_norm_sub _ (rho P' u) _).trans
      apply le_trans (add_le_add hL (show ‖rho P' u - _‖ ≤ 4*e from ?_)) he.heat
      have h0 : ‖rho P' u - rho (collect G A') u‖ = ‖rho R u‖ := congr_arg norm (by unfold R rho; dsimp only [Pi.sub_apply]; abel)
      change ‖rho P' u - rho (collect G A') u‖ ≤ _
      rw [h0]
      apply (norm_sub_le ..).trans ((add_le_add ((norm_sub_le ..).trans (add_le_add ((norm_add_le ..).trans
        (add_le_add b.2.2 c.2.2)) u'.2.2)) d'.2.2).trans_eq (by unfold e; ring))
    have hh := (norm_le_norm_sub_add (G.curvature ξ) P0).trans (add_le_add hX hZ)
    have hx : ‖G.curvature ξ‖≤ t/32 := hh.trans (by unfold a coolFraction; linarith only [ht])
    change G.chord ξ ≤ t/8
    nlinarith only [hξ,pow_le_pow_left₀ (norm_nonneg _) hx 2,ht,G.chord_nonneg ξ]

lemma throughout (E : Config G f) (L : ℕ) (r : Site f) (Z : Gaussian.Vec (In (retime x) A F (G:=G))) (l : Dir G f)
    {w : ℕ} (P : Patch) (U : Teller G) (he : Enlightened P U w x β) (hW : w*walls (betaF G x P.L)=L)
    (k : Incidence G f→ℂ) (hU : 2*(L+1)< f.val)
    (hr : ∀ i∈Room r L,G.chord (E i) ≤ highPrice G*linkRoom x ∧ ‖G.curvature (E i)-collect G (l+coupling β • breadth Z) i‖ ≤ edgeFire G x)
    (j : Incidence G f) (hj : separation r j.1+2≤ L) (f' : Site f→G.El) (Y' : Config G f) (hY' : Lattice.gauge f' Y'=E)
    (hμ : |((coupling β)⁻¹ • Work.F03.faceCurl (fromBead G j) l) j.2.2-(k j).re| ≤ x^(-(1/16):ℝ)) :
    let g:= coupling β
    |rigid (coloring (f' r) (Tapes.kiosk g r Y')) j- ((k j).re + (dKeys A F (retime x) *ᵥ Z) (toPAC j))|≤ x^(-(1/32):ℝ) := by
  intro g; have hg:=coupling_pos he.sparks; let z:=breadth Z; let f:=highPrice G*linkRoom x; let e:=edgeFire G x
  have hL : ∀ u ∈ Room r L, G.chord (Lattice.gauge f' Y' u) ≤ f := by rw [hY']; exact fun u hu=> (hr u hu).1
  have h0 := crested Y' hU hg (mul_nonneg ((twin_price G).choose_spec.choose_spec.choose_spec.1) (linkRoom_pos he.stable).le) f' j hj hL
  let hn := nautical G f g L
  let Z':= fun i => g⁻¹ • G.curvature (E i); let u:=froth Z' j
  have ht : |rigid (coloring (f' r) (Tapes.kiosk g r Y')) j-u| ≤ hn := by rw [hY'] at h0; exact h0
  obtain hy:= he.helm; rw [hW] at hy; apply le_trans _ hy
  let Y0 := collect G (l+g • z); let V:= g⁻¹ • Y0
  have hK : |u-froth V j| ≤ 4*(e/g) := by
    apply four_corners j hj
    intro i hI; change ‖g⁻¹ • G.curvature (E i)-g⁻¹ • Y0 i‖ ≤ _
    rw [← smul_sub,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hg).le,← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right (hr i hI).2 hg.le
  let u' := fromBead G j
  let a:= Work.F03.faceCurl u' l
  have hx : froth V j = (g⁻¹ • a) j.2.2 + (dKeys A F (retime x) *ᵥ Z) (toPAC j) := by
    let m:=Work.F03.faceCurl u' z
    have hh : rho V u'=g⁻¹ • a+m := by
      unfold V; have ht : rho (g⁻¹ • Y0) u'= g⁻¹ • rho Y0 u' := by unfold rho; simp only [Pi.smul_apply,smul_sub,smul_add]
      rw [ht,show rho Y0 u'=a+g • m from (curl_formula ..|>.symm.trans (joined_curl u' l z g)),smul_add,smul_smul,inv_mul_cancel₀ hg.ne', one_smul]
    rw [froth,rigid,hh,rainShift,PiLp.add_apply]; rfl
  let m:= (dKeys A F (retime x) *ᵥ Z) (toPAC j)
  apply (abs_sub_le _ u _).trans; apply (add_le_add ht (le_trans (abs_sub_le _ (froth V j) _) (add_le_add hK ?_))).trans_eq (add_assoc ..).symm
  rw [hx,add_sub_add_right_eq_sub]
  exact hμ

section model
variable {C : Family G} (B : Binding C) {N i p : ℕ}
local notation "St" => C.path.levels.clock.op i p
local notation "x" => C.path.levels.clock.hatBeta i
local notation "y" => betaF G (C.path.levels.clock.hatBeta i) (C.S.block i)
local notation "J" => C.path.levels.clock.J i
local notation "T" => tunnel B N i p
local notation "Θ" => tell B i
variable (M : C.Makes) (hi : i<N) (hh : C.path.levels.clock.J (i+1)=C.path.levels.clock.J i)
variable {w W : ℕ} {A : Stores (C.path.levels.clock.op i p)} {β β' U d : ℝ}
    {V : Config G (C.side i p)}

include M hi hh
/-- Main nonlinear observable bound on actual Rank stencil (subsequently use
at paths and for copies). Given the large-enough Pose & payments on both x's, on
every indicated mask:
1. The PHOTO U in these shared variables is itself valid on the fine field patch,
even testing every flag at the boundary; not claimed this covers Frozen throughout the volume.
2. Rank's arguments on f (input of W) that gauges to U, even in this *same held
sample*, are close to the critical bias on the actual coarse V plus the
fluctuation curl (using `Coupling` and `dKeys` precisely).
The errors hold simultaneous where tested, not on unguarded Y.
No translating color indices or identifying expectations across outside configurations. -/
lemma laminate (h : Steady G (C.S.block i) (B.prices.Ω J) x (B.prices.α J) β β') (he : Enlightened (C.path.levels.clock.op i p).patch Θ w x β) (hf : StrongScope (C.path.levels.clock.op i p).patch Θ U x) (o W) (v : Dir G (C.side i p)) (hP : Pose A o W x V v) (k : (C.path.levels.clock.op i p).Choices) (q : Chi)
    (F : Forest (C.path.levels.clock.op i p).ratio) (Y : RoomView A (retime x) F G) (r : Site (C.side (i+1) p))
    (hU : 2*(w*walls y+1)<(C.side (i+1) p).val) (hv : Guards (parasol r (w*walls y)) Y.2 (haze G x β (C.S.block i)))
    (hY : ∀ e∈parasol r (w*walls y), separation o ((C.path.levels.clock.op i p).ratio.parent e.1)+walls x+2 ≤ W) (hc : 100*(1+radiusB (retime x)) ≤ (C.side i p).val) :
    let V' := spine V o
    let L:= w*walls y; let Q:= Spindle.patch L r; let Z:= Y.2
    let U:= gazed T k q V' (retime x) β d Y
    let g:=coupling β
    Healthy (phase y) Q U ∧ ∀ f (t : Site (C.side (i+1) p) → G.El), Lattice.gauge t f = U →
      ∀ j : Incidence G (C.side (i+1) p), separation r j.1 + 2 ≤ L →
        |rigid (coloring (t r) (Tapes.kiosk g r f)) j- ((purseMean B (i:=i) o V (coupling β') (N:=N) j).re + (dKeys A F (retime x) *ᵥ Z) (toPAC j))| ≤ x^(-(1/32):ℝ) := by
  intro V' L Q Z E g
  have hV := ships B N i p M hi
  have hS:= B.sized i p; let l:=low T F v; let z:= breadth Z
  let K := linkRoom x; let f:= highPrice G*K; let e:=edgeFire G x; let t:=phase y; let a:=coolFraction; have ha : 0<a:=coolFraction_pos
  have ht : 0<t:=alpha_phase _ (add_pos_of_pos_of_nonneg h.visible (Work.E04.shift_nonneg G (C.S.block i)))
  have hg : 0<g := coupling_pos h.sparks
  have hM := hf.sight St T rfl hV hS hc (B.world.H N (i+1)) (B.world.H N i)
    (B.prices.η (C.path.levels.clock.J (i+1))) _ _ _ (B.prices.eta_pos _) (B.prices.eta_pos J)
    (B.pays.all N (i+1) hi _) (B.pays.all N i hi.le _) (B.paths N (i+1) hi p)
    (B.sworn N (i+1) hi p) (B.pays.crossings N i p hi) (knot B N i p M hi) _ A o V v hP F k q d .endpoint Y.1
  have hr j (h : j∈parasol r L) := slide_link k q T hP F Y hV he hM.1 j (le_trans (Nat.le_add_right _ _) (hY j h)) h hv
  have hp (u : Cell (C.side (i+1) p)) (hR : bones u ⊆ parasol r L) : G.chord (faceValue E u) ≤ t/8 := by
    have hr' := (pointing B hi hh hP h F u (hY (u.1,u.2.val.1) (hR (first_bone u)))).1
    exact checkingMask (parasol r L) E u hR (C.path.levels.clock.op i p).patch Θ he l z g t e ht rfl rfl (fun i hi=>hr i hi) hr'
  refine ⟨?_,fun Y' f' hY' j hj => ?_⟩
  · apply Finset.disjoint_left.mpr
    intro u h0 hs; obtain ⟨i,hi,he⟩:= (flags_spec ..).mp hs
    have h := hp i (shade_heel.flags _ ⟨u,h0,hi⟩)
    change t < _ at he; linarith only [he,h,ht]
  have hu : (j.1,j.2.1.val.1)∈Room r L := (therm L r (fromBead G j) hj).1
  have hy := (pointing B hi hh hP h F (fromBead G j) (hY (j.1,j.2.1.val.1) (Room_advances (Nat.le_add_right L 8) hu))).2 j.2.2
  exact throughout E L r Z l (C.path.levels.clock.op i p).patch Θ he rfl (purseMean B (i:=i) (N:=N) o V (coupling β')) hU (fun i hi=>(hr i (Room_advances (Nat.le_add_right L 8) hi)).2) j hj f' Y' hY' hy
end model
end YM.PhysicalNext.InteractingRank
