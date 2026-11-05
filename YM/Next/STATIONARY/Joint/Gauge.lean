import YM.Next.STATIONARY.Joint.Chart


set_option autoImplicit false
/-!
# Changing from arbitrary rooted joint fields to a forest station

Shrink chart around (1,1), coarse V~1, before comparison. `boots` strips
all the way to Φ=1 and uses tree normalization on *physical* links. The
coarse input (when interpreting V) stays fixed. Replica included in the
additive chart at all uses.
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Wilson Exterior Precision Bloch Laurent Filter Tree Matrix
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators
variable {G : Gauge} {c f : Side} {S : StepData c f}

section gauge
variable (S) (F : Forest S.ratio)

def abode (V : Config G c) (z : AxisChart G F) : Joint G c f := (lifting F V z,1)
@[simp] lemma abode_zero : abode S F (1:Config G c) 0=1 := by simp [abode]

lemma merit_pin (t : S.Choices) (p : Clip) (R : PathData G) (V : fieldDir G c 1) (a : AxisChart G F) :
    muster S t p R (represent V) (abode S F (represent V) a) = tested F t p R V a := by
  rw [tested,muster,tickets,ribbon]; simp only [abode,Lattice.gauge,Pi.one_apply,one_mul,inv_one,mul_one]; rfl

def trousers (U : Joint G c f) := (wages S (U.2 ∘ S.ratio.parent) 1 U).1
def boots (U : Joint G c f) : Coats G f := F.foldAt (trousers S U) * (U.2 ∘ S.ratio.parent)
def cloak (U : Joint G c f) := wages S (boots S F U) 1 U
def clerk (V : Config G c) (U : Joint G c f) : AxisChart G F :=
    fun i => plogC G ((cloak S F U).1 i*(replica S.ratio V i)⁻¹)

lemma cloak_wick (U : Joint G c f) : cloak S F U = (Profiles.wiped F (trousers S U),1) := by
  rw [cloak,boots,show (1:Coats G c)=(1:Coats G c)*1 from (one_mul 1).symm, ← wage_comp]
  refine Prod.ext rfl ?_; funext i
  simp [wages,F.fold_root,Ratio.embed_parent]
lemma cloak_compress (U : Joint G c f) (i : ↥F.trunks) : (cloak S F U).1 i=1 := by rw [cloak_wick]; exact F.compress _ _ i.property
lemma cloak_sits (V : Config G c) (a : AxisChart G F) : cloak S F (abode S F V a)=abode S F V a := by
  rw [cloak_wick]; refine Prod.ext ?_ rfl
  rw [show trousers S (abode S F V a)=(abode S F V a).1 by
    rw [trousers,show (abode S F V a).2 ∘ S.ratio.parent=1 from rfl,wages_zero]]
  change Profiles.wiped F (F.drape _)=_
  rw [← Profiles.wears, Profiles.wick_root]; rfl
@[simp] lemma cloak_zero : cloak S F (1:Joint G c f)=1 := by rw [← abode_zero S F]; exact cloak_sits ..
@[simp] lemma clerk_zero : clerk S F (1:Config G c) 1=0 := by funext i; simp [clerk]

section parameter
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {x : X}
    {V : X → Config G c} {U : X → Joint G c f}

lemma drape_lit {W : X → Config G f} (p : Army W x) : Army (fun z => F.foldAt (W z)) x := by
  have hp (a : Walk) (i : Site f) : ContDiffAt ℝ ω (fun z => G.mat (travel (W z) i a)) x := by
    induction a generalizing i with
    | nil => exact contDiffAt_const
    | cons k t ih =>
      simp only [travel,G.mat_mul]; refine ContDiffAt.mul ?_ (ih _)
      unfold Step.read; split
      · exact p.inv _
      exact p _
  intro i
  exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (hp (F.hike i) i)
lemma boot_lit (p : Thaw U x) : Army (fun z => boots S F (U z)) x :=
    let he : Army (fun z i => (U z).2 (S.ratio.parent i)) x := fun _ => p.2 _
    (drape_lit S F (W:=fun z => trousers S (U z)) (he.slant p.1)).mul he
lemma cloak_lit (p : Thaw U x) : Thaw (fun z => cloak S F (U z)) x :=
    p.wages S (boot_lit S F p) (Army.park _ _)

omit F in
lemma copy_lit (p : Army V x) : Army (fun z => replica S.ratio (V z)) x := by
  intro i; simp only [ replica]; split
  · exact contDiffAt_const
  exact p _
lemma abode_lit (h : Army V x) {z : X → AxisChart G F} (hz : ContDiffAt ℝ ω z x) : Thaw (fun y => abode S F (V y) (z y)) x := by
  refine ⟨fun i => ?_,Army.park 1 x⟩
  by_cases he : i∈F.trunks
  · simp_rw [abode,lifting,show ∀ a : F.Slice G, F.drape a i=1 from fun a => F.on_tree a ⟨i,he⟩]
    exact contDiffAt_const
  let j : F.Free := ⟨i,he⟩
  have he (y : X) : (abode S F (V y) (z y)).1 i=G.lieExp (z y j)*replica S.ratio (V y) i := F.off_tree _ j
  simp_rw [he,G.mat_mul]
  exact ((G.exp_jet.contDiffAt).comp (f:=fun y => z y j) _ ((contDiffAt_pi.mp hz) _)).mul (copy_lit S h i)

lemma cloak_return (p : Thaw U x) (u : U x=1) (q : Army V x) (v : V x=1) : ∀ᶠ z in 𝓝 x, cloak S F (U z)=abode S F (V z) (clerk S F (V z) (U z)) := by
  have hp (i : F.Free) : ∀ᶠ z in 𝓝 x, (cloak S F (U z)).1 i = (abode S F (V z) (clerk S F (V z) (U z))).1 i := by
    let A z := (cloak S F (U z)).1 i*(replica S.ratio (V z) i)⁻¹
    have ht : ContinuousAt A x := (((continuous_apply _).continuousAt.comp (cloak_lit S F p).1.cont)).mul (((continuous_apply _).continuousAt.comp (copy_lit S q).cont).inv)
    have he : clerk S F (V x) (U x)=0 := by rw [u,v,clerk_zero]
    filter_upwards [(show Tendsto A _ (𝓝 1) from (show A x=1 by simp [A,u,v]) ▸ ht.tendsto).eventually G.plog_right] with z hz
    rw [show (abode S F (V z) (clerk S F (V z) (U z))).1 i = G.lieExp (plogC G (A z))*replica S.ratio (V z) i from F.off_tree _ i, show G.lieExp (plogC G (A z))=_ from hz]; unfold A; simp
  filter_upwards [eventually_all.mpr hp] with z hz
  refine Prod.ext ?_ (by rw [cloak_wick]; rfl)
  funext i; by_cases h : i∈F.trunks
  · exact (cloak_compress S F _ ⟨i,h⟩).trans (F.on_tree _ ⟨i,h⟩).symm
  exact hz ⟨i,h⟩
lemma clerk_lit (p : Thaw U x) (u : U x=1) (q : Army V x) (v : V x=1) :
    ContDiffAt ℝ ω (fun z => clerk S F (V z) (U z)) x := by
  refine contDiffAt_pi.mpr fun i => ContDiffAt.comp (g:=G.plog)
    (f:=fun z => G.mat ((cloak S F (U z)).1 i*(replica S.ratio (V z) i)⁻¹)) _ ?_ ?_
  · simp only [u,v,cloak_zero,Prod.fst_one,replica_one,Pi.one_apply,inv_one,mul_one,G.mat_one]; exact G.plog_diff
  exact ((cloak_lit S F p).1 _).mul ((copy_lit S q).inv _)

lemma clerk_abode {a : X → AxisChart G F} (hu : ContDiffAt ℝ ω a x) (h : a x=0) :
    ∀ᶠ y in 𝓝 x, clerk S F (V y) (abode S F (V y) (a y))=a y := by
  suffices he : ∀ᶠ y in 𝓝 x, ∀ i : F.Free, clerk S F (V y) (abode S F (V y) (a y)) i=a y i from he.mono fun _ hx => funext hx
  refine eventually_all.mpr fun i => ?_
  have hx := ((contDiffAt_pi.mp hu) i).continuousAt.tendsto
  simp only [h,Pi.zero_apply] at hx
  filter_upwards [hx.eventually G.plog_left] with y hy
  rw [clerk,cloak_sits,abode,lifting]; dsimp only; rw [F.off_tree,mul_inv_cancel_right]; exact hy
end parameter
end gauge
end YM.Stationary
end

/-! # Exact covariance in rooted left coordinates. Fixed fine AND coarse gauge. -/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Wilson Exterior Precision Bloch Laurent Filter Tree Matrix
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {c f n : Side} {S : StepData c f}

lemma adjoint_exp (u : G.El) (a : G.Color) : G.lieExp (G.adjoint u a)=u*G.lieExp a*u⁻¹ := by
  apply G.mat_injective; rw [G.mat_mul,G.mat_mul,G.mat_lieExp,G.mat_lieExp,G.mat_adjoint,G.exp_conjugate]; rfl
lemma plog_conj (u : G.El) : ∀ᶠ v : G.El in 𝓝 1, plogC G (u*v*u⁻¹)=G.adjoint u (plogC G v) := by
  have he : Tendsto (plogC G) (𝓝 1) (𝓝 0) :=
    by
      have he := G.plog_diff.continuousAt.tendsto.comp (G.continuous_mat.tendsto 1)
      rw [G.plog_one] at he
      exact he
  have hv : Tendsto (G.adjoint u) (𝓝 0) (𝓝 0) := by simpa using (LinearMap.continuous_of_finiteDimensional (G.adjoint u)).tendsto 0
  filter_upwards [G.plog_right,(hv.comp he).eventually G.plog_left] with v hv hy
  rw [← show G.lieExp (G.adjoint u (plogC G v))=u*v*u⁻¹ from (adjoint_exp ..).trans (by rw [show G.lieExp (plogC G v)=v from hv])]; exact hy

-- no product spin determinant until counting blocks finite.
def armorG (u : Coats G n) : BaseSites G n →L[ℝ] BaseSites G n :=
    let A := ContinuousLinearMap.pi (fun i => (G.adjoint (u i)).toContinuousLinearMap ∘L ContinuousLinearMap.proj i)
    gaugeColor.symm.toContinuousLinearMap ∘L A ∘L gaugeColor.toContinuousLinearMap
def armor (u : Coats G n) : Link G n →L[ℝ] Link G n :=
    let A := ContinuousLinearMap.pi (fun i : Edge (Site n) => (G.adjoint (u i.1)).toContinuousLinearMap ∘L ContinuousLinearMap.proj i)
    edgeColor.symm.toContinuousLinearMap ∘L A ∘L edgeColor.toContinuousLinearMap

lemma armorG_at (u : Coats G n) (b : BaseSites G n) (x : Site n) : gaugeColor (armorG u b) x=G.adjoint (u x) (gaugeColor b x) := by simp [armorG]
lemma armor_at (u : Coats G n) (b : Link G n) (e : Edge (Site n)) : edgeColor (armor u b) e=G.adjoint (u e.1) (edgeColor b e) := by simp [armor]

def armUp (k : Coats G f) (u : Coats G c) : Vault G c f →L[ℝ] Vault G c f := (armor k).prodMap (armorG u)
lemma armor_go (u : Coats G n) (a : Link G n) (V : Config G n) :
  input _ _ (armor u a)*Lattice.gauge u V = Lattice.gauge u (input _ _ a*V) := by
    funext e
    simp only [Pi.mul_apply,Lattice.gauge,input_color,armor_at,adjoint_exp]; group
lemma arm_root (k : Coats G f) (u : Coats G c) (b : Vault G c f) (U : Joint G c f) :
    Stationary.extend (armUp k u b)* wages S k u U=wages S k u (Stationary.extend b * U) := by
  refine Prod.ext (armor_go ..) ?_
  funext i; change switchSite (armorG u b.2) i * (u i * U.2 i * _) = u i * ((switchSite b.2 i)*U.2 i) * _
  simp only [switch_color,armorG_at,adjoint_exp]; group

variable (S) (t : S.Choices) (p : Clip) (R : PathData G)
/-- Rooted left direction at arbitrary configuration. -/
def canon (V : Config G c) (U : Joint G c f) (b : Vault G c f) :=
    muster S t p R V (Stationary.extend b * U)

def Shell (V : Config G c) (U : Joint G c f) :=
    ContDiffAt ℝ ω (canon S t p R V U) 0 ∧ fderiv ℝ (canon S t p R V U) 0=0

lemma canon_carry (h : S.patch.Branches S.kernel G) {σ A Λ : ℝ} (hp : R.Bounds p σ A Λ)
    (V : Config G c) (U : Joint G c f) (k : Coats G f) (u : Coats G c) :
    (canon S t p R (Lattice.gauge u V) (wages S k u U)) ∘ (armUp k u) = canon S t p R V U := by
  funext x; simp only [Function.comp_apply,canon, arm_root,root_wages S t h _ _ _ p R hp]

lemma gauge_one (U : Config G n) : Lattice.gauge (1:Coats G n) U=U := by
  funext x; simp [Lattice.gauge]
lemma gauge_right (U : Config G n) (u : Coats G n) : Lattice.gauge u⁻¹ (Lattice.gauge u U)=U := by
  funext x; simp [Lattice.gauge]; group

variable {S t p R}
lemma Shell.wage (h : S.patch.Branches S.kernel G) {σ A Λ : ℝ} (hp : R.Bounds p σ A Λ)
    {V : Config G c} {U : Joint G c f} (he : Shell S t p R V U) (k : Coats G f) (u : Coats G c) :
    Shell S t p R (Lattice.gauge u V) (wages S k u U) := by
  let F := canon S t p R V U
  let A := armUp k⁻¹ u⁻¹
  have hv := canon_carry S t p R h hp (Lattice.gauge u V) (wages S k u U) k⁻¹ u⁻¹
  rw [wage_comp,inv_mul_cancel,inv_mul_cancel,wages_zero,gauge_right] at hv
  unfold Shell; rw [← hv]
  have H : ContDiffAt ℝ ω F (A 0) := by rw [map_zero]; exact he.1
  refine ⟨H.comp _ A.contDiff.contDiffAt,?_⟩
  have e := fderiv_comp (0:Vault G c f) (g:=F) (f:=A) (H.differentiableAt (by simp)) (A.differentiableAt)
  rw [map_zero, show fderiv ℝ F 0=0 from he.2, ContinuousLinearMap.zero_comp] at e
  exact e
lemma Shell.chain {V : Config G c} {W : Joint G c f} {p' : Clip} (p : Shell S t p' R V W)
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {U : X → Joint G c f} {x : X}
    (h : Thaw U x) (he : U x=W) : fderiv ℝ (fun z => muster S t p' R V (U z)) x=0 := by
  let f z := U z * W⁻¹
  have hu : f x=1 := by simp [f,he]
  have ht : Thaw f x := h.mul (Thaw.fixed _ _)
  have hh : (fun z => muster S t p' R V (U z))=ᶠ[𝓝 x] canon S t p' R V W ∘ (fun z => retract (f z)) := by
    filter_upwards [(show Tendsto f _ (𝓝 1) from hu ▸ ht.cont.tendsto).eventually extend_retract] with y hy
    simp only [Function.comp_apply,canon,hy,f,inv_mul_cancel_right]
  have e := fderiv_comp x (g:=canon S t p' R V W) (f:=fun z => retract (f z)) (by rw [hu,retract_one]; exact p.1.differentiableAt (by simp)) ((ht.log hu).differentiableAt (by simp))
  rw [hu,retract_one,p.2,ContinuousLinearMap.zero_comp] at e
  exact hh.fderiv_eq.trans e
end YM.Stationary
end

/-! # Extend the already-proved RScene graph to rooted all-joint stationarity.

Also gauge-equivalence of such stationary families near trivial fields with
an arbitrary smooth parameterization of the V output. Collapse before comparing
on every finite mesh. All tags, still near identity for the analytic statements.
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Wilson Exterior Precision Bloch Laurent Filter Tree Matrix
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators
variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio}

variable (F)

def encamp (ρ : Bid.Dir G c → AxisChart G F) (z : Link G c) :=
    abode S F (input G c z) (ρ (arm G c 1 z))
variable {F} {ρ : Bid.Dir G c → AxisChart G F} {p : Clip} {R : PathData G}
    (h : Critical F p R ρ)
include h
omit h in
lemma camp_claim (t : S.Choices) (z : Link G c) : muster S t p R (input G c z) (encamp F ρ z) =
    tested F t p R (arm _ _ _ z) (ρ (arm _ _ _ z)) := merit_pin ..
lemma encamp_zero : encamp F ρ 0=1 := by simp [encamp,h.1]
lemma camp_thaw : Thaw (encamp F ρ) 0 := by
  have hv := h.2.1
  let Q := arm G c 1
  apply abode_lit _ _ (Army.powL (v:=id) (contDiffAt_id (x:=(0:Link G c))))
  exact (show ContDiffAt ℝ ω ρ (Q 0) by rw [map_zero]; exact hv).comp (f:=fun v => Q v) _ Q.contDiff.contDiffAt

variable (hb : S.patch.Branches S.kernel G) {σ A Λ : ℝ} (hp : R.Bounds p σ A Λ)
include hb hp

lemma camp_station (t : S.Choices) :
    ∀ᶠ z in 𝓝 (0:Link G c), Shell S t p R (input _ _ z) (encamp F ρ z) := by
  let W := fun z : Link G c => ρ (arm G c 1 z)
  have hh : ContDiffAt ℝ ω W 0 := by
    refine ContDiffAt.comp (g:=ρ) (f:=arm G c 1) _ ?_ (arm _ _ _).contDiff.contDiffAt
    rw [map_zero]; exact h.2.1
  have hh' : W 0=0 := by simp [W,h.1]
  let X (z : Point G c f) := Stationary.extend z.2 * encamp F ρ z.1
  let V (z : Point G c f) := input G c z.1
  have he : Thaw X 0 :=
    (Thaw.through (v:=Prod.snd) contDiffAt_snd).mul (Thaw.comp (g:=encamp F ρ) (camp_thaw h) (w:=Prod.fst) (x:=(0:Point G c f)) contDiffAt_fst)
  have hX : X 0=1 := by simp [X, encamp_zero h]
  have hu : Army V 0 := Army.powL contDiffAt_fst
  have hV : V 0=1 := by simp [V]
  let L := fun z : Point G c f => clerk S F (V z) (X z)
  have hL : ContDiffAt ℝ ω L 0 := clerk_lit S F he hX hu hV
  have hi : ∀ᶠ z in 𝓝 0, muster S t p R (V z) (X z)=tested F t p R (arm G c 1 z.1) (L z) := by
    filter_upwards [cloak_return S F he hX hu hV] with z hz
    have H := root_wages S t hb (X z) 1 (boots S F (X z)) p R hp (V z)
    rw [gauge_one] at H
    rw [← merit_pin,← H]; exact congr_arg (muster S t p R (V z)) hz
  let K := fun z : Link G c => (z,(0 : Vault G c f))
  have hk : Tendsto K (𝓝 0) (𝓝 0) := tendsto_id.prodMk_nhds tendsto_const_nhds
  have hd := he.earn hb t (by rw [hX]; rfl) hu hp
  have ht : Tendsto (arm G c 1) (𝓝 0) (𝓝 0) := by simpa using (arm G c 1).continuous.tendsto 0
  filter_upwards [ht.eventually (h.2.2 t |>.2), clerk_abode S F (V:=fun z : Link G c => input G c z) hh hh', hk.eventually (hd.eventually (by simp)), hk.eventually (eventually_eventually_nhds.mpr hi),hk.eventually (hL.eventually (by simp))] with z hr hf hd H hM
  have hk : ContDiffAt ℝ ω (canon S t p R (input G c z) (encamp F ρ z)) 0 := Work.F05.hold_jet (V:=fun a => canon S t p R (input G c a) (encamp F ρ a)) (x:=z) (y:=0) hd
  refine ⟨hk,?_⟩
  have ht : L (z,0) = W z := by
    change clerk S F (input G c z) (Stationary.extend (0:Vault G c f) * encamp F ρ z)=W z
    rw [extend_zero,one_mul]; exact hf
  have hl := Work.F05.hold_jet (V:=fun a b => L (a,b)) hM
  have hu := Work.F05.hold_near (x:=z) (y:=(0:Vault G c f)) (V:=fun z => muster S t p R (V z) (X z)=tested F t p R (arm G c 1 z.1) (L z)) H
  have hx : HasFDerivAt (tested F t p R (arm _ _ _ z)) (0 : AxisChart G F →L[ℝ] ℝ) (L (z,0)) := by rw [ht]; exact hr
  have hv := (hx.comp 0 (hl.differentiableAt (by simp) |>.hasFDerivAt))
  exact (hv.congr_of_eventuallyEq hu).fderiv

section veterans
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [FiniteDimensional ℝ X]
    {u : X → Joint G c f} {z : X → Link G c} {b : ℝ}
/-- Local, same representative after stripping. Allows additional analytic
parameters (coarse gauges, chart changes etc). -/
lemma veterans (hy : PriceGap F p R b) (hk : 0<b) (t : S.Choices)
    (hw : Thaw u 0) (he : u 0=1) (hi : ContDiffAt ℝ ω z 0) (hx : z 0=0)
    (hs : ∀ᶠ x in 𝓝 0, Shell S t p R (input G c (z x)) (u x)) :
    ∀ᶠ x in 𝓝 0, cloak S F (u x)=encamp F ρ (z x) := by
  let Q x := arm G c 1 (z x)
  let V x := input G c (z x)
  let L x := clerk S F (V x) (u x)
  have hQ : ContDiffAt ℝ ω Q 0 := (arm _ _ _).contDiff.contDiffAt.comp _ hi
  have hQ' : Q 0=0 := by simp [Q,hx]
  have hL := cloak_return S F hw he (V:=V) (Army.powL hi) (by simp [V,hx])
  have hG : ∀ᶠ x in 𝓝 0, fderiv ℝ (tested F t p R (Q x)) (L x)=0 := by
    filter_upwards [hs,hL] with x hq ht
    have hg := hq.wage hb hp (boots S F (u x)) 1
    rw [gauge_one] at hg; change Shell _ _ _ _ (V x) (cloak S F (u x)) at hg; rw [ht] at hg
    have hu := hg.chain (x:=L x) (U:=fun a => abode S F (V x) a) (abode_lit S F (Army.park (V x) _) contDiffAt_id) rfl
    change fderiv ℝ (fun a => muster S t p R (represent (Q x)) (abode S F (represent (Q x)) a)) _=_ at hu
    simp_rw [merit_pin] at hu; exact hu
  let J x := tested F t p R (Q x)
  have hg : ContDiffAt ℝ ω (uncurry J) 0 :=
    (show ContDiffAt ℝ ω (uncurry <| tested F t p R) (Q 0,0) by rw [hQ']; exact h.2.2 t |>.1).comp (g:=uncurry (tested F t p R)) (f:=fun y : X × AxisChart G F => (Q y.1,y.2)) _ ((hQ.comp (g:=Q) (f:=Prod.fst) (0:X × AxisChart G F) contDiffAt_fst).prodMk contDiffAt_snd)
  have hj (x : AxisChart G F) : Work.F05.bend (J 0) 0 x x = 0 → x = 0 := fun hv => Classical.byContradiction (fun hz => (Work.F05.tested_diag hk hy t x hz).ne' (by simpa only [J,hQ'] using hv))
  have hm : Tendsto Q (𝓝 0) (𝓝 0) := hQ' ▸ hQ.continuousAt.tendsto
  have ht : L 0=0 := by simp [L,hx,V,he]
  have hf : Tendsto L (𝓝 0) (𝓝 0) := ht ▸ (clerk_lit S F hw he (V:=V) (Army.powL hi) (by simp [V,hx])).continuousAt.tendsto
  have hv : Tendsto (ρ ∘ Q) (𝓝 0) (𝓝 0) := h.1 ▸ h.2.1.continuousAt.tendsto.comp hm
  have H := Work.F05.station_unique hg hj hf hv hG (hm.eventually (h.2.2 t |>.2) |>.mono (fun a ha => ha.fderiv))
  filter_upwards [hL,H] with a hc ha
  rw [hc, show clerk S F (V a) (u a)=ρ (Q a) from ha]; rfl
end veterans
end YM.Stationary
end

/-! # First-jet dictionary, routed oriented links. In `Depot` the repaired
Fourier kernel is installed on the actual ratio; no grid extension here.
Recenter cap(U) has derivative `-fixRoot`. -/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Wilson Exterior Precision Bloch Laurent Filter Tree Matrix
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {c f n : Side}

-- Install matrix scalar-like in each color slot, coordinate conversion to additive real tuples.
def uniformM {k m : ℕ} (W : Matrix (Body k c) (Body m f) ℝ) : Corn (Lines G f m) →L[ℝ] Corn (Lines G c k) := LinearMap.toContinuousLinearMap {
    toFun a j := (W *ᵥ parts G m (arm _ _ _ a) j.2.2) (j.1,j.2.1)
    map_add' a b := by funext i; exact congr_fun (Matrix.mulVec_add W (parts G m (arm _ _ _ a) i.2.2) (parts G m (arm _ _ _ b) i.2.2)) _
    map_smul' b a := by funext i; exact congr_fun (Matrix.mulVec_smul W b (parts G m (arm _ _ _ a) i.2.2)) _ }

lemma uniformC {k m : ℕ} (W : Matrix (Body k c) (Body m f) ℝ) (v : Corn (Lines G f m)) (i) :
    parts G k (arm _ _ _ (uniformM W v)) i=W *ᵥ parts G m (arm _ _ _ v) i := by funext x; rfl
lemma first_uniform (b : BaseSites G n) : gradientA G n b=uniformM (d 0 n) b := by
  apply edgeColor.injective
  ext ⟨x,i⟩ j
  change arm _ _ _ (gradientA G n b) _ _ = _
  rw [gradientC]
  change _ = (d 0 n *ᵥ parts G 0 (arm _ _ _ b) j) (x,coord i)
  rw [d_sites]; rfl

lemma ray_id {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (x : X) : HasDerivAt (fun t : ℝ => t • x) x 0 := by
    simpa using! (hasDerivAt_id' (0:ℝ)).smul_const x

lemma ray_swap {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {V : X → Y} (h : DifferentiableAt ℝ V (0:X)) {x : X} {y : Y} (he : HasDerivAt (fun t : ℝ => V (t • x)) y 0)
    {u : ℝ → X} (p : u 0=0) (hp : HasDerivAt u x 0) : HasDerivAt (fun t : ℝ => V (u t)) y 0 := by
  have ht := he.unique (Push.side V h x)
  have hh : HasFDerivAt V (fderiv ℝ V 0) (u 0) := by rw [p]; exact h.hasFDerivAt
  rw [ht]; exact hh.comp_hasDerivAt 0 hp

-- If the matrix derivative lies in lie (indeed follows from having derivative but supplied), read exact tangent in Color.
lemma ray_recall {u : ℝ → G.El} (h : u 0=1) {a} (he : HasDerivAt (fun t => G.mat (u t)) (G.colorMat a) 0) :
    HasDerivAt (fun t => plogC G (u t)) a 0 := by
  have hh := G.plog_diff.differentiableAt (by simp) |>.hasFDerivAt
  have hp : HasDerivAt (fun t : ℝ => plogC G (G.lieExp (t • a))) a 0 := by
    apply (ray_id a).congr_of_eventuallyEq
    exact (show Tendsto (fun t : ℝ => t • a) (𝓝 0) (𝓝 0) from by simpa using (ray_id a).continuousAt.tendsto).eventually G.plog_left
  have ht := hp.unique (show HasDerivAt (fun t : ℝ => plogC G (G.lieExp (t • a))) ((fderiv ℝ G.plog 1) (G.colorMat a)) 0 from
      (HasFDerivAt.comp_hasDerivAt 0 (show HasFDerivAt G.plog (fderiv ℝ G.plog 1) (G.mat (G.lieExp ((0:ℝ) • a))) by
        rw [zero_smul,G.mat_lieExp_zero,G.mat_one]; exact hh) (exp_ray a)))
  exact ht ▸ HasFDerivAt.comp_hasDerivAt 0 (show HasFDerivAt G.plog (fderiv ℝ G.plog 1) (G.mat (u 0)) by rw [h,G.mat_one]; exact hh) he

lemma ray_power (b : BaseSites G c) (i) : HasDerivAt (fun t : ℝ => G.mat (switchSite (t • b) i)) (G.colorMat (gaugeColor b i)) 0 := by simp_rw [switch_color,map_smul,Pi.smul_apply]; exact exp_ray _
lemma ray_input (b : Link G c) (i) : HasDerivAt (fun t : ℝ => G.mat (input G c (t • b) i)) (G.colorMat (edgeColor b i)) 0 := by simp_rw [input_color,map_smul,Pi.smul_apply]; exact exp_ray _
lemma ray_frame {u : ℝ → Coats G n} {a : BaseSites G n} (h : u 0=1) (hp : ∀ i, HasDerivAt (fun x => G.mat (u x i)) (G.colorMat (gaugeColor a i)) 0) : HasDerivAt (fun x => frameLog (u x)) a 0 := by
  have he : HasDerivAt (fun x i => plogC G (u x i)) (gaugeColor a) 0 :=
    hasDerivAt_pi.mpr fun i => ray_recall (by rw [h]; rfl) (hp i)
  conv => arg 2; rw [← ContinuousLinearEquiv.symm_apply_apply gaugeColor a]
  exact gaugeColor.symm.hasFDerivAt.comp_hasDerivAt 0 he
lemma ray_content {u : ℝ → Config G n} {a : Link G n} (h : u 0=1) (hp : ∀ i, HasDerivAt (fun x => G.mat (u x i)) (G.colorMat (edgeColor a i)) 0) : HasDerivAt (fun x => content (u x)) a 0 := by
  have he : HasDerivAt (fun x i => plogC G (u x i)) (edgeColor a) 0 :=
    hasDerivAt_pi.mpr fun i => ray_recall (by rw [h]; rfl) (hp i)
  have hp z : content z=edgeColor.symm (fun i => plogC G ((z : Config G n) i)) := by
    apply edgeColor.injective; rw [edgeColor.apply_symm_apply]; funext i; exact content_at z i.1 i.2
  simp_rw [hp]
  conv => arg 2; rw [← ContinuousLinearEquiv.symm_apply_apply edgeColor a]
  exact edgeColor.symm.hasFDerivAt.comp_hasDerivAt 0 he
lemma ray_gauged {u : ℝ → Coats G n} {a : BaseSites G n} {U : ℝ → Config G n} {A : Link G n}
    (h : u 0=1) (hp : ∀ i, HasDerivAt (fun x => G.mat (u x i)) (G.colorMat (gaugeColor a i)) 0)
    (he : U 0=1) (ht : ∀ i, HasDerivAt (fun x => G.mat (U x i)) (G.colorMat (edgeColor A i)) 0) (i : Edge (Site n)) :
    HasDerivAt (fun x => G.mat (Lattice.gauge (u x) (U x) i)) (G.colorMat (edgeColor (A-gradientA G n a) i)) 0 := by
  have hv : edgeColor (gradientA G n a) i=gaugeColor a (i.1+step i.2)-gaugeColor a i.1 := gradientC ..
  simp only [Lattice.gauge,G.mat_mul,G.mat_inv]; convert! ((hp i.1).mul (ht i)).mul ((hp (i.1+step i.2)).star) using 1
  simp only [map_sub,Pi.sub_apply,hv,h,he,Pi.one_apply,G.mat_one,mul_one,one_mul,Pi.mul_apply,G.colorMat_skew,star_one]; abel

variable {S : StepData c f} (h : S.patch.Branches S.kernel G) (t : S.Choices)
include h

lemma rooted_cap (b : Link G f) (i : Site c) : HasDerivAt (fun v : ℝ => G.mat (bears S t (input G f (v • b)) i))
    (-G.colorMat (gaugeColor (uniformM (fixRoot S) b) i)) 0 := by
  let a := arm G f 1 b
  let d j := Push.tap S i j a - Push.tap S i S.patch.center a
  let L := uniformM (G:=G) (fixRoot S)
  have hp j : HasDerivAt (fun v : ℝ => G.mat (S.frames (input G f (v • b)) t.1 i j)) (G.colorMat (d j)) 0 := by
    simp_rw [input,map_smul]; exact Push.derivative S h i t.1 j a
  have he : HasDerivAt (fun v : ℝ => prospect S t (input G f (v • b)) i) (G.colorMat (∑ j,S.patch.weight j • d j)) 0 := by
    unfold prospect; rw [map_sum]; simp only [map_smul]
    exact HasDerivAt.fun_sum (fun j _ => (hp j).const_smul (S.patch.weight j))
  have hh : gaugeColor (L b) i = -(∑ j, S.patch.weight j • d j) := by
    ext k; change (fixRoot S *ᵥ parts G 1 a k) (i,vac) = _
    let p : G.Color →ₗ[ℝ] ℝ := LinearMap.comp (LinearMap.proj k) (WithLp.linearEquiv 2 ℝ _).toLinearMap
    change _=p (-(∑ j, S.patch.weight j • d j))
    rw [map_neg,map_sum]; unfold d; simp_rw [map_smul,map_sub,fixRoot,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply,adjusted,LinearMap.sub_apply,LinearMap.sum_apply,LinearMap.smul_apply,smul_sub,Finset.sum_sub_distrib,← Finset.sum_smul,S.patch.weight_sum,one_smul]
    have hv j : p (Push.tap S i j a)=tau S i j (parts G 1 a k) := Push.tap_line S i a j k
    simp_rw [hv]; abel
  have ht := Push.focused _ he (by rw [zero_smul, input_zero,prospect_zero S t h])
  rw [Submodule.starProjection_eq_self_iff.mpr (G.colorMat_mem _)] at ht
  rw [show uniformM (fixRoot S) b=L b from rfl,hh,map_neg,neg_neg]; exact ht

lemma centered_pred (x : Vault G c f) (i : Edge (Site c)) :
    HasDerivAt (fun v : ℝ => G.mat (ribbon S t (enroll S t (Stationary.extend (v • x))) i))
        (G.colorMat (edgeColor (uniformM (Precision.mean S) x.1-gradientA G c x.2) i)) 0 := by
  let k := x.2+uniformM (fixRoot S) x.1
  let F := fun v : ℝ => enroll S t (Stationary.extend (v • x))
  have hF : F 0=1 := by simp [F,enroll_zero S t h]
  have hp j : HasDerivAt (fun v => G.mat ((F v).2 j)) (G.colorMat (gaugeColor k j)) 0 := by
    convert! (ray_power x.2 j).mul (rooted_cap h t x.1 j).star using 1
    simp [k,bear_zero S t h,Gauge.colorMat_skew]
  let A := uniformM (probe S) x.1
  have he i : HasDerivAt (fun v => G.mat (S.prediction (F v).1 t i)) (G.colorMat (edgeColor A i)) 0 := by
    change HasDerivAt (fun v : ℝ => G.mat (S.prediction (input _ _ (v • x.1)) t i)) _ _
    simp_rw [input,map_smul]; exact Push.prices S h i t _
  have hg : A-gradientA G c k= uniformM (Precision.mean S) x.1-gradientA G c x.2 := by
    suffices hz : A=uniformM (Precision.mean S) x.1 + gradientA G c (uniformM (fixRoot S) x.1) by
      unfold k; rw [hz,map_add]; abel
    funext z; change (probe S *ᵥ parts G 1 (arm _ _ _ x.1) z.2.2) (z.1,z.2.1)=_
    rw [probe,add_mulVec,← Matrix.mulVec_mulVec,Pi.add_apply]
    simp only [first_uniform]; rfl
  rw [← hg]; apply ray_gauged (U:=fun v => S.prediction (F v).1 t) (u:=fun v => (F v).2)
    (by rw [hF]; rfl) hp _ he
  rw [hF]; exact funext (fun e => Push.settled S h e t)
end YM.Stationary
end
