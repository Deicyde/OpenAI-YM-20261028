import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Syllabus
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Song.Octet
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Song.Score



/-! # Export a preliminary physical all-field step

This has exact equality to the full integral using the one Coarse law and
 local intake. Keeps the F normalization, includes Hou and complete eligible
 inventory. Uses projections/corrections with signs of `earlyValue` in
 Downstream. Has quantitative Local but at a provisional perturbation size
 which will not fit projection width. No Claim Width from these exports.
 `old` data H set once along a career. Refrain Annual pad independent
 of replanning Cash. Still pointwise, separate from Compared. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Song
open Function Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset VerifiedReset.Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Greenbelt Match Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {I R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i : ℝ} {k j n ℓ : ℕ} {F : Tree.Forest S.ratio}
variable (p : BudgetPoint) (H : Cash W s μ L Q o α T I) {J : Cash W s μ L Q o α T R}
    (X : Match.Alliance H J 1 0) (χ : Chi) (γ : ℝ)

lemma layer_spread {ι : Type} (w : ι → Config G c → ℝ) (V : Config G c) (s : Signed) (b : Site c) : layer w (pull s b V)=layer w V := by
  unfold layer; rw [← Equiv.sum_comp (Seat.move s b) (fun i:Seat c => ∑' j,w j (i.view V))]; simp_rw [Seat.view_move]; rfl
lemma bill_spread (A : ℕ → Atom G k) {σ C : ℝ} (hp : 0<σ) (h : SumBudget (fun i=> (A i).budget σ) C) (V : Config G c) (s : Signed) (b : Site c) : billOf p A (pull s b V)=billOf p A V := by
  let g V (i:Stave (n:=c)):=factor*1*(A i.2).placed p (i.1.view V) 0
  let e:Equiv.Perm (Stave (n:=c)):=Equiv.prodCongr (Seat.move s b) (Equiv.refl _)
  have hx (V:Config G c) : HasSum (g V) (billOf p A V) := by
    have hx:= allocated p A V 1 hp h; simp_rw [couponA] at hx
    rwa [one_mul] at hx -- inside? factor*1 not one_mul
  refine (hx _).tsum_eq.symm.trans ((Eq.trans ?_ (e.tsum_eq (g V))).trans (hx V).tsum_eq)
  apply tsum_congr; intro i; unfold g; change _=factor*1*(A i.2).placed p (Seat.view (Seat.move s b i.1) V) 0; rw [Seat.view_move]; rfl
lemma harmony (h : Cash.Renewed n a δ e J) (V : Config G c) (t : Seat c) : Real.log (J.homesteadPool χ (t.view V))=Real.log (J.homesteadPool χ V) := by
  obtain ⟨π⟩:= J.laws.intake.cap.labels.moves t.1 (S.ratio.embed t.2)
  rw [(J.threshold_logPool χ (t.view V) h).1,(J.threshold_logPool χ V h).1]; change (∑' u,J.trainedPool χ (pull t.1 t.2 V) u)=∑' u,J.trainedPool χ V u
  simp_rw [incensed J χ π V]; exact (swing J π).furrow.tsum_eq _

abbrev ballad : Type := Seat c × Magazine H

scoped instance : Countable (ballad H) := by
  have : Countable (Head S) := inferInstance
  unfold ballad Magazine Cash.fragrances; infer_instance
scoped instance : Infinite (ballad H) := by unfold ballad Magazine Songbook Tally Stave; infer_instance

def pennant : ℕ≃ballad H := numbering _
def posting : Listing G c := ⟨revolve (scaleT p H) ∘ pennant H, Refrain.reserve H ∘ Refrain.badge H⟩
def plusone : Collection.Source G c := ⟨choir (opus H X χ γ) ∘ pennant H, fuse H X χ ∘ Refrain.badge H⟩

theorem motion (U : Signed) (b : Site c) : Nonempty (((posting p H).read (plusone H X χ γ)).Moves U b) := by
  obtain ⟨π⟩ := J.laws.intake.cap.labels.moves U (S.ratio.embed b)
  obtain ⟨η,hη⟩ := settles H X χ U b π
  let e := whirl (ι:=Magazine H) U b; let a:=pennant H; let k:=badge H
  let A:=(posting p H).read (plusone H X χ γ)
  have hk i : k (congo k η i)=_ := perch k η i; have ha i : a (congo a e i)=_ := perch a e i
  let h x:= spirit (scaleT p H) (opus H X χ γ) U b x
  refine ⟨⟨congo a e,congo k η,fun i=>?_,fun i=>?_,fun i=>?_,fun i=>?_,fun i V=>?_,fun i V=>?_,fun i V=>?_⟩⟩
  · change (revolve _ (a (congo a e i))).site=_; rw [ha]; exact (h _).1
  · change (revolve _ (a (congo a e i))).support=_; rw [ha]; exact (h _).2.1
  · change (reserve H (k (congo k η i))).support=_; rw [hk]; exact (hη _).1
  · change (reserve H (k (congo k η i))).inventory=_; rw [hk]; exact (hη _).2.1
  · change (reserve H (k (congo k η i))).extraTest V ↔ _; rw [hk]; exact ((hη (k i)).2.2 V).1
  · change choir _ (a (congo a e i)) V=_; rw [ha]; exact congr_fun (h (a i)).2.2 V
  change fuse H X χ (k (congo k η i)) V=_; rw [hk]; exact ((hη (k i)).2.2 V).2

def token (_J : Cash W s μ L Q o α T R) (χ : Chi) (F : Tree.Forest S.ratio) := Next.Fluctuations.Sector.prefactor S G R.beta * Real.exp (R.v*Fintype.card (Site f))* (prism T s χ o.K 1 F).deducted Q.table R.beta

def weighty (J : Cash W s μ L Q o α T R) (χ : Chi) (F : Tree.Forest S.ratio) := Real.log (token J χ F)/(Fintype.card (Site c):ℝ)

variable (N : Captain J j C' d v Y A b r B q k χ) (O : Tree.Forest S.ratio) (hp : p.threshold=Pressure.temp s) (hP : p.order ≤ j)
    (hB : p.B=radiusB s) {σ C Λ : ℝ} (hx : T.down.Bounds T.low σ C Λ) (h : Cash.Renewed n a δ e J)
include hp
lemma grants (V : Config G c) : overhead (prism T s χ o.K V O) R Q.table= Real.exp (weighty J χ O* Fintype.card (Site c) -(R.beta*averaged (fun x=> ∑ i:Pressure.Cell c, T.down.baseTerm T.low p (pull x 0 V) i))) := by
  have he : token J χ O * Raw.stone T R.beta s V= overhead (prism T s χ o.K V O) R Q.table := by unfold overhead levy token; rw [mul_right_comm]; rfl
  have hz : 0<token J χ O := pos_of_mul_pos_left (he.symm ▸ overhead_pos (prism T s χ o.K V O) J) (Real.exp_nonneg _)
  rw [← he, Raw.stone_full _ _ V p hp, weighty, div_mul_cancel₀ _ (show (Fintype.card (Site c):ℝ)≠0 from by positivity), sub_eq_add_neg, Real.exp_add,Real.exp_log hz, neg_mul]

include h hP N hx
lemma forward (V : Config G c) :
    earlyValue (posting p H) T.down T.low p (plusone H X χ γ) R.beta (weighty J χ O) γ V=S.push R.beta R.eval V := by
  let r:= (posting p H).read (plusone H X χ γ)
  have ht t := language p H X χ N hp hP γ h hx (Seat.view t V)
  have hz : ∀ t: Seat c, HasSum (fun i=> masked p.threshold (scaleT p H i).support (opus H X χ γ i) (Seat.view t V)) (-(Real.log (J.homesteadPool χ V)) + (-(γ*Collection.receipt T.down T.low p V+(R.beta*(billOf p T.down.cubic V+billOf p T.down.quartic V)+billOf p T.down.loop V)))) := by
    intro t; have hb:= ht t; rw [harmony χ h V t,Seat.view, Collection.receipt, layer_spread,
      bill_spread p _ hx.width hx.three,bill_spread p _ hx.width hx.four,bill_spread p _ hx.width hx.two] at hb; exact hb
  have hd := voices (scaleT p H) (opus H X χ γ) p V _ hz
  have hL : r.additive p V=_ := ((pennant H).hasSum_iff.mpr hd).tsum_eq
  let X':= prism T s χ o.K V O; let y:=overhead X' R Q.table; let C := J.homesteadPool χ V
  have hg : r.gas p V=∑' i,J.canopyPool χ V i := inundated p H X χ ((posting p H).reg) (plusone H X χ γ).logRead V h hp
  have hu : HasSum (fun u=> y*C*J.canopyPool χ V u) (S.push R.beta R.eval V) := J.convoyPool χ V h O
  have he : y*C*r.gas p V=S.push R.beta R.eval V := by rw [hg, ← tsum_mul_left]; exact hu.tsum_eq
  have hm : Real.exp (weighty J χ O * Fintype.card (Site c)- T.down.inChannels T.low p R.beta V - r.additive p V)*Real.exp (-γ* Collection.receipt T.down T.low p V)=y*C := by
    rw [← Real.exp_add,chan, hL, show y=_ from grants p (J:=J) χ O hp V]
    have hv : 0<C := by unfold C; rw [← (J.threshold_logPool χ V h).2]; positivity
    rw [← Real.exp_log hv,← Real.exp_add]; apply congr_arg Real.exp
    unfold C at *; ring
  unfold earlyValue RG.Rep.eval; rw [mul_right_comm (Real.exp _)]; change Real.exp _*Real.exp _*r.gas p V=_; exact Eq.trans (congr_arg (·*r.gas p V) hm) he

include hB
lemma loaded (Hh : preExponent p ≤ a) (ht : Armada Q L μ a s i B j k) (hn : p.power ≤ ℓ) (hd : WilsonStartup.Decent T.low p) (hw : preExponent p / p.B ≤ σ/2) :
    Collection.Local (posting p H) p (plusone H X χ γ) (turnFee p*((collars G i s j ℓ*(salary Q L μ B s j k*(1-1/2)⁻¹)) + octaveNeed G p T.low σ C Λ R.beta γ)) (Cash.armK Q L μ s 0 n) := by
  obtain ⟨f,hf,hF⟩ := books p H X χ N hp hP hB γ Hh ht hn hd hx hw
  obtain ⟨hc,hh⟩:= spiral _ _ f (fun i=> (hF i).1) (fun i=> (hF i).2) hf
  refine ⟨fun i=> (hc (pennant H i)).1, qualified p H X χ (posting p H).reg _ hp, motion p H X χ γ, ⟨_,fun i=> (hc (pennant H i)).2,fun i=> Cost.equiv (pennant H) (hh i)⟩,?_⟩
  exact chargesOut p H X χ h hB (by unfold preExponent at Hh; linarith)
end YM.PhysicalNext.Repeat.Song
