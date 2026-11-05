import YM.WilsonBulk.Build.Noisy

/-!
# Unmasked bulk step re-expression on one finite mesh

Use at cover Ward & horizontal/affine kernel tests. Includes every
frame and step tag, preserving physical beta germ, and *no* RP quotient or
renormalized Z-cumulants. Applies to arbitrary output log supplied by the Heat
constructor via script, on symmetric positive data with leading Hess factored.
All order equality at level BEFORE kinetic readjustment. Used for Ward,
leading kinetic & inherited plate. Not a norm estimate on these analytic
changes (take in *infinite* cover as exact for such coefficient rule).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Atelier
open Function Filter Matrix Sheet Precision RG Exterior Lattice Wilson FreeResolvent
open Stationary (Army)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open Coursing
variable {α β A κ ι : Type} [CommRing A] [Algebra ℝ A] [Fintype κ] [Fintype ι]
variable {G : Gauge} {c f n : Side} {S : StepData c f} {F L : Coursing ι S} {P Q : Bed} {J : ChartRatio G} {a : ℝ} {k : G.El}
variable {u v : Tabletop κ→Interface G c}
variable {M N : Logbook G f} {W Z : Logbook G c}
variable {t : Tabletop κ→ Site c→G.El}
variable (s : Signed) (b : Site c)

def festival (t : Tabletop κ→Site c→G.El) (z : Tabletop κ) : Carries G S := Carries.send S s b (constantGauge (t z) S.ratio)
omit [Fintype κ] in
lemma festival_visit (z : Tabletop κ) (U : Config G f) : (festival s b t z : Carries G S).routeG U=Lattice.gauge (constantGauge (t z) S.ratio) (pull s (S.ratio.embed b) U) := rfl
lemma fold_origin (F : Tree.Forest S.ratio) : F.foldAt (1:Config G f)=1 := by
  ext1 i; unfold Tree.Forest.foldAt; rw [show travel (1:Config G f) _ (F.hike i)=1 from ?_,inv_one]; rfl
  exact (link_one (G:=G)).symm ▸ Push.stroll_zero .. -- inspect
lemma parades (hu : ContDiffAt ℝ ω u 0) (hh : Army t 0) (h : t 0 = Function.const _ k) : Legible (festival s b t) F P u := by
  constructor
  · let D:=lower (LegsT G ι) κ; let j (z:Secrets G ι κ):= t (D z)
    let w:=signal G f ∘ palace G F P u; let H := pull s (S.ratio.embed b) ∘ w
    have he : Army j 0:= (show Army t (D 0) from (D.map_zero).symm ▸ hh).comp (w:=D) D.contDiff.contDiffAt
    have hx : Army (fun z=>constantGauge (j z) S.ratio) 0:= fun i=> he _
    have hp : Army w 0:= signal_force (palace_jet G hu)
    exact hx.slant (army_spin s _ hp)
  rw [festival_visit,h,show (pull s _ (1:Config G f))=1 from ?_]
  · exact gauge_absolute
  rw [← signal_zero,← swivel_sign,swivel_birth]

-- path germ relation including varying overlay and private root material

def auditorium (S : StepData c f) (t : S.Choices) (φ : Logbook G f) := submit (exposure (upper (Pennant G f) (Pennant G c))) φ + gossip G S t
lemma foyer (i : S.Choices) (φ : Logbook G f) (t : S.Choices) (h : S.patch.Branches S.kernel G) : auditorium S t φ= auditorium S i φ := by
  unfold auditorium; unfold gossip; rw [ink_of (f:=canonWeight G S t) (g:=canonWeight G S i) ?_]
  let g:= signal G f ∘ upper (Pennant G f) (Pennant G c)
  have hv : g 0=1:= by simp only [g,Function.comp_apply,map_zero,signal_zero]
  have hh : Tendsto g (𝓝 0) (𝓝 1) := hv ▸ ((signal_cont G f).comp (upper _ _).continuous).tendsto (0:ReadingV G c f)
  filter_upwards [hh.eventually (Work.F04.prediction_germ (S:=S) h t i)] with z hz
  unfold canonWeight noiseTaylor; dsimp only [g,Function.comp] at hz; rw [hz]
lemma auditorium_start (i : S.Choices) (h : S.patch.Branches S.kernel G) (hm : Steps 1 M (grains (matrixK G f P))) : Steps 1 (auditorium S i M) (ambient (matrixK G f P) (probeX G S) S.kernel.penalty) := by
  let U:=submit (exposure (upper (Pennant G f) (Pennant G c))); let K:=matrixK G f P
  have he : U (grains K)=forceQ K (privateName (ι:=Pennant G c)):= by unfold U grains; rw [forceQ_map]; simp_rw [submit_named,upper_code]
  have h₁ := hm.push U (by rw [show U PowerSeries.X=PowerSeries.X from submit_X _,PowerSeries.constantCoeff_X]); rw [show U (grains (matrixK G f P))=_ from he] at h₁
  exact h₁.add (gossip_line i h).2

structure Plays (u v : Tabletop κ→Interface G c) (t : Tabletop κ→Site c→G.El) : Prop where
  source : ContDiffAt ℝ ω u 0
  ends : ContDiffAt ℝ ω v 0
  quiet : u 0=0
  sitting : v 0=0
  encores : ∃ k:G.El,t 0=Function.const _ k
  val : Army t 0
  oriented : ∀ᶠ z in 𝓝 0,signal G c (v z)= Lattice.gauge (t z) (pull s b (signal G c (u z)))

lemma moving (r i : S.Choices) (hl : S.patch.Branches S.kernel G) (h : Plays s b u v t)
    (hd : Dances N) (ht : Spins s (S.ratio.embed b) M N) :
    let θ:= lands (festival s b t) F L P u v
    submit (exposure (porch G F P u)) (auditorium S i M)=switch (exposure θ) (submit (exposure (porch G L P v)) (auditorium S r N)) := by
  intro θ
  obtain ⟨k,hk⟩:= h.encores; let D:=lower (LegsT G ι) κ
  have hh : Legible (festival s b t) F P u:= parades s b h.source h.val hk
  have hx : ContDiffAt ℝ ω (ride θ) 0:= ride_jet θ (lands_jet _ _ _ _ _ _ h.quiet h.ends hh)
  have hc : ride θ 0=0:= ride_zero θ (lands_origin _ _ _ _ _ _ h.quiet h.sitting hh.arrived)
  let T z:=constantGauge (t (D z)) S.ratio
  let U := porch G F P u; let V:= porch G L P v∘ ride θ
  let B := upper (Pennant G f) (Pennant G c); let p:= lower (Pennant G f) (Pennant G c)
  let f':= signal G f ∘ B∘ U; let W z:=Lattice.gauge (T z) (pull s (S.ratio.embed b) (f' z)); let g z:= L.tree.foldAt (W z)*T z
  have hw : Army W 0:= hh.plays
  have he z : T z ∘ S.ratio.embed=t (D z):= by ext1 i; simp [T, constantGauge,S.ratio.embed_parent]
  have hg : Army g 0 := (Stationary.drape_lit S L.tree hw).mul (fun i:Site f=> (show Army (t∘D) 0 from Stationary.Army.comp (show Army t (D 0) from (D.map_zero).symm ▸ h.val) D.contDiff.contDiffAt) (S.ratio.parent i))
  have hU : ContDiffAt ℝ ω U 0:= porch_jet G h.source; have hv : ContDiffAt ℝ ω (porch G L P v) 0:= porch_jet G h.ends
  have Hx : U 0=0:= porch_zero _ h.quiet; have Hy : V 0=0:= by unfold V Function.comp; rw [hc, porch_zero _ h.sitting]
  have Hx' : (B ∘ U) 0=0:= by rw [Function.comp_apply,Hx,map_zero]
  have Hy':(B ∘ V) 0=0:= by rw [Function.comp_apply,Hy,map_zero]
  have hV : ContDiffAt ℝ ω V 0:= (hc.symm ▸ hv).comp _ hx
  have hf : f' 0=1:= by unfold f'; rw [Function.comp_apply,Hx',signal_zero];
  have hW : W 0=1:= by
    rw [show W 0=(festival s b t (D 0)).routeG (f' 0) from rfl,map_zero,hf]; exact hh.arrived
  have hp : g 0=Function.const _ k:= by unfold g T; rw [map_zero,hW,fold_origin,one_mul,hk]; rfl
  have hp' z : g z∘ S.ratio.embed=t (D z) := funext fun i=> by unfold g Function.comp; rw [Pi.mul_apply,L.tree.fold_root, one_mul]; exact congr_fun (he z) i
  have hz : ∀ᶠ z in 𝓝 0,signal G f (B (V z))=Lattice.gauge (g z) (pull s (S.ratio.embed b) (f' z)) := (into_loom _ _ L _ u v h.quiet hh).mono (fun z hz=> by
    rw [show g z=_ from (show g z=L.tree.foldAt (W z)*T z from rfl), ← followGauge]; exact hz)
  let j:= S.withinChoice s b r
  rw [← ride_pull θ,exposure_encode hx hv hc (porch_zero _ h.sitting), foyer j M i hl]; unfold auditorium; rw [map_add,map_add]; refine congrArg₂ (·+·) ?_ ?_
  · rw [exposure_encode hU B.contDiff.contDiffAt Hx (map_zero _), exposure_encode hV B.contDiff.contDiffAt Hy (map_zero _)]
    exact (rhythm s _ hg hp (B.contDiff.contDiffAt.comp _ hU) (B.contDiff.contDiffAt.comp _ hV) Hx' Hy' hd ht hz).symm
  apply PowerSeries.X_pow_mul_cancel (k:=2)
  have hc (A : Secrets G ι κ→ReadingV G c f) (i : S.Choices) (hA : ContDiffAt ℝ ω A 0) (ha : A 0=0) : PowerSeries.X^2*submit (exposure A) (gossip G S i)= ink (canonWeight G S i ∘ A) := by rw [ink_comp (canonWeight_jet _ hl) hA ha,← (gossip_line i hl).1,map_mul,map_pow,submit_X]
  rw [hc U j hU Hx,hc V r hV Hy]; apply ink_of
  filter_upwards [hz,(D.continuous.continuousAt.tendsto.eventually (D.map_zero.symm ▸ h.oriented))] with z H h'
  change noiseTaylor S (signal G c (u (D z))) (f' z) j=noiseTaylor S (signal G c (v (D (ride θ z)))) (signal G f (B (V z))) r
  rw [show D (ride θ z)=D z from lower_ride ..,h',H,← hp',noise_ward (g z) _ _ r hl,noise_spin s b _ _ _ hl]
end YM.WilsonBulk.Atelier
