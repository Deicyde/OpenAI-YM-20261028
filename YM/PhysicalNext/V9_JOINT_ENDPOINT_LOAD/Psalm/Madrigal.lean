import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Roster
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Stage

/-! # Withdrawing at the physical authenticated step inputs

At either transition, retaining the exact directed setup (incl the
selected forest and shared tag data upon invocation, not imposing one
on their assemblies). Not constructing the Directed/Bake & its income,
kin or `Sworn`! Also direct calls at Wired iterative horizons where
kernel admissibilities are backed without those realizations. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Psalm.Stage
open Function Filter Set Lattice RG Wilson Pressure Tree Precision Bid Exterior Bloch
    Next Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.SectorMeasure.Presented SectorNext.Remainder SectorNext.Remainder.Affine
    AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
    Heir Clockwork Testing RG.Supply Push.PriceCompiler Shoot Heir.Suite UVNext.PricedKernels Folio Input
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {Z : ChartRatio G} {s : Sheet G} {K : MapPrices} {D : Rolls s} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {C : Programs s} {d : ℕ → ℕ → Record} {P Q : ℕ→ℕ→ℝ} {w : ℕ→ℕ→ℝ} {r : ℕ→ℕ→ℕ} {F : ℕ→ℕ→Cafe}
    {Bt : Baton G} {t : ℕ→ℕ→Menu} {b : ℕ→ℕ→ Booth} {J : ℕ→ℕ→Aux}
    {a : Levels G} {m p N : ℕ}
variable {T : Tube G (Suite.Studio a m p)} {u : Rep G (a.S.side (m+1) p)} (hL : Listens W C d w Bt F t) (hb : Funded Z K F b t w W) (hp : Paid I a) (ht : u.p=a.budget (m+1))
    (hc : Enabled s K C d P Q r a m p T) (hu : u.beta∈band a (m+1))
include hL hp ht hc hu
lemma authorized : let j := fine a m; let i := coarse a m; let D' := desk hb hp m p T u
    Sounded (query s K j i) (C j i) (d j i) Bt (F j i).r D' ∧ Gliss (d j i) D' D'.out.order := by
  intro j i D'; let S:=a.clock.op m p; have hT := hc.make; rw [← ht] at hT
  have hF := hT.bulletin.priced
  have hr := hL j _ (hp.pays m) i (step_paid a m) (first_le hp m) S.patch rfl (block_eq hp m)
  have hd : D'.out.order = (s.profile i).order := congr_arg RG.Stage.order (params_eq hp m)
  refine ⟨⟨hT,(show S.kernel=s.kernel from hF.knobs).symm ▸ hr.1,hc_heat _ _ ?_,by rw [show D'.input=u from rfl,hT.rehearsed.fiery_eq]; rfl⟩,
    hd.symm ▸ hr.2 D' rfl rfl ?_ rfl hT.rehearsed.fiery_eq⟩
  · have ht := hu.1; have hh := a.fits.delayed (m+1); change 0<u.beta; linarith
  simpa only [show S.patch.L=D.L j from block_eq hp m, ← (show a.clock.hatBeta (m+1)=betaF G (a.clock.hatBeta m) (D.L j) from beta_eq hp m)] using! hu.1
where hc_heat {G : Gauge} {c f : Side} (S : StepData c f) (d : Desk G S) (h : 0 < d.input.beta) : 0 < d.g := coupling_pos h

structure Cadence (Z : ChartRatio G) (K : MapPrices) (W : Delays Θ) (b : ℕ→ℕ→Booth) (t : ℕ→ℕ→Menu) (w : ℕ→ℕ→ℝ) (F : ℕ→ℕ→Cafe) (C : Programs s) (Bt : Baton G) (d : ℕ→ℕ→Record) (P Q : ℕ→ℕ→ℝ) (r : ℕ→ℕ→ℕ) (J : ℕ→ℕ→Aux) : Prop where
  early : Earlier s K C P Q r
  plan : Funded Z K F b t w W
  covers : Offers K W C d r
  supplements : Secured b Z K F t J W
  hears : Listens W C d w Bt F t
  marked (j i : ℕ) : (t j i).θ ≤ (d j i).ε/32

structure Prosody (s : Sheet G) (K : MapPrices) (b : ℕ→ℕ→Booth) (t : ℕ→ℕ→Menu) (F : ℕ→ℕ→Cafe) (C : Programs s) (Bt : Baton G) (d : ℕ→ℕ→Record) (P Q : ℕ→ℕ→ℝ)
    (r : ℕ→ℕ→ℕ) (J : ℕ→ℕ→Aux) (a : Levels G) (m p : ℕ) (D' : Desk G (Suite.Studio a m p)) : Prop where
  enabled : Enabled s K C d P Q r a m p D'.tube
  swept : let j:=fine a m; let i:=coarse a m; Sweep (J j i) (query s K j i) (F j i) (b j i) (t j i) D'
  sounds : let j:=fine a m; let i:=coarse a m; Sounded (query s K j i) (C j i) (d j i) Bt (F j i).r D'
  gliss : Gliss (d (fine a m) (coarse a m)) D' D'.out.order
  marked : let j:=fine a m; let i:=coarse a m; (t j i).θ ≤ (d j i).ε/32

variable (h : Cadence Z K W b t w F C Bt d P Q r J)
omit hc hL
include h hp ht hu
lemma sing (hT : Lift.Booth (query s K (fine a m) (coarse a m)) (Suite.Studio a m p) T) (h₀ : Seam T (wide K (fine a m) (coarse a m)) (Suite.scale K (fine a m) (coarse a m))) :
    Prosody s K b t F C Bt d P Q r J a m p (desk h.plan hp m p T u) := by
  have he := Suite.enabled h.covers h.early hp T hT h₀
  obtain ⟨hf,hz⟩ := authorized h.hears h.plan hp ht he hu
  exact ⟨he,equipped h.supplements h.plan hp m p T hT.1 _ hu,hf,hz,h.marked ..⟩

omit h hp in
lemma wired {B : Before} {f : ℕ→ℕ} {D : Rolls (B.sheet G f)} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y} {M : Preparations B D} {C : Programs (B.sheet G f)}
    (h : Cadence Z (B.frozen G) W b t w F C Bt d P Q r J) (hP : Permit M I a) {H : Horizon a} {Q' : ℕ→ℕ→PathData G} (hv : Motor B a H) (hq : Installed B a H Q') (hm : m<N) :
    Prosody (B.sheet G f) (B.frozen G) b t F C Bt d P Q r J a m p (desk h.plan hP.paid m p (Permit.tube H Q' N m p) u) := by
  have he := tickets (N:=N) p H Q' hm hP hv hq h.covers h.early
  obtain ⟨hf,hz⟩ := authorized h.hears h.plan hP.paid ht he hu
  exact ⟨he,equipped h.supplements h.plan hP.paid m p _ he.make.bulletin.priced u hu,hf,hz,h.marked ..⟩

omit hp ht hu
variable {Post : PostCost D} (B : Directed G I Z K Post) {u : Rep G (B.a.S.side (m+1) p)}
theorem directed (hm : m<N) (hu : u.beta∈band B.a (m+1)) (he : Lives B.bake N (m+1) p u) (hS : ∀ i∈({m,m+1}:Set ℕ), Sworn (B.M.H N i) (B.a.S.side i p) G) :
    let D' := assigned h.plan m p B N u
    Prosody s K b t F C Bt d P Q r J B.a m p D' ∧ ∀ A F κ V, A.flags=RG.flags (temp D'.betaHat) V → D'.Valid ∧ (spectacle D' A F κ).Clearing V ∧ Admitted A F D'.betaHat V κ Z D'.allocation D'.radius := by
  intro D'; have hv := Suite.directed p hm B hS h.covers h.early
  obtain ⟨hf,hz⟩ := authorized h.hears h.plan B.valid he.point hv hu
  exact ⟨⟨hv,equipped h.supplements h.plan B.valid m p _ (proceeds B N m p hm) u hu,hf,hz,h.marked ..⟩,(aboard h.plan m p B N u hm he hu).2⟩
end YM.PhysicalNext.JointLoad.Psalm.Stage
