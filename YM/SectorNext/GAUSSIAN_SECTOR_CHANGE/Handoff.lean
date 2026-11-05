import Mathlib.Analysis.Fourier.Convolution
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.ROTATIONS.Charge
import YM.Next.SCHEDULE.Air
import YM.Next.SCHEDULE.GridCost
import YM.Next.SCHEDULE.Levels
import YM.Push.CUTOFF_PROJECTORS.Equations
import YM.Push.SECTOR_MEASURE.Consumer
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Stamped







set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# License the committed RG integral

Global disjoint/program call keeps the same forests / tags / monitors
/ alpha path.

Gives exact equality (head or ∫∫ on completed tags as in
licenses), incl membership paths to read LIC at true β.

Read *for each*
F -- no replacing parts by integrals on new slices.

Boost stamp shows one
way to buy all late assumptions together with schedule and energy
numerics *upstream of* Wait (not imposing that an arbitrary realized
trajectory can now be reissued).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix Gaussian Rows
open YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid YM.Push.SectorMeasure
open YM.Next.Fluctuations.Sector YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented
open Wisps Tier Schur LocalJet
open Input RG.Supply RG.Shoot Scheduling
open YM.Pressure.Testing
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} (Z : ChartRatio G) (K : MapPrices) {B : Sheet G} (D : Rolls B)
variable {T : Protection D}

/-- Post-L price for the step j→i. Also covers intact even case of
actual-V mismatch via Admitted (Licenses then derived separately). -/
structure Starcash (pays : ℝ) (j i : ℕ) (w a E : ℝ) : Prop where
  door : 0 < a
  ceil : 0 < E
  stars (x : ℝ) : pays ≤ x →
    let L := D.L j
    let d := a * fiery G x L
    0 < d ∧ 2*d < firstRadius G ∧ 4*d < Z.radius ∧
      (∀ t : G.Color, ‖t‖ ≤ 4*d → |Real.log (Z.J t)| ≤ E*‖t‖^2) ∧
      ∀ (c f : Side) (S : StepData c f), S.patch.J=j → S.patch.L=L → 100*(1+radiusB x) ≤ c.val →
      ∀ U : Tube G S, (query B K j i).Funds S U →
      100*macroR S.patch ≤ f.val ∧ 1<c.val ∧
      ∀ (A : Stores S) (F : Forest S.ratio) (p : Allocation G S x w) (k : S.Choices) (V : Config G c) (q : Chi),
        Admitted A F x V k Z p d ∧ (A.flags=RG.flags (temp x) V → ∀ β : ℝ,0<β →
          Permitted x V k A F p Z d β (fog A F U x V k) (meanLog A F U x V k q d) ∧
          (Rows.gram U x V k (shots S x) A F).PosDef ∧ (∃ B, 0<B ∧ Authorized A V F x B))

private lemma buying (hZ : LocalRatio Z) {j i : ℕ} (w : ℝ) (hw : 0<w) (H : 4≤j) : ∃ x a E : ℝ, Starcash Z K D x j i w a E := by
  · let P : Teller G := query B K j i
    let S : Patch := ⟨D.L j,j,H,(D.large j).size,(D.large j).odd⟩
    obtain ⟨C,E,hc,he,hh⟩ := sponsored_permit P Z hZ S (B.has S) w hw
    obtain ⟨x,hx⟩ := eventually_atTop.mp hh
    refine ⟨x,C,E,hc,he,fun b hv => ?_⟩
    obtain ⟨hr,hp,hl,hs,hQ⟩ := hx b hv
    intro l d
    refine ⟨hp,hl,hs,hr,fun c f T h ht hg U hu => ?_⟩
    have he : T.patch=S := by
      rcases heq : T.patch with ⟨L,J,H,h1,h2⟩; rw [heq] at h ht
      change L = D.L j at ht
      change J = j at h
      subst_vars; rfl
    obtain ⟨hi,hh,h⟩ := hQ c f T U he hg hu
    exact ⟨hi,hh,fun A F P k V q => h A F k V P q⟩


/-- Store all bills across admissible transitions. -/
def Cosmos {D : Rolls B} {T : Protection D} (W : Delays T) (g a E : ℕ → ℕ → ℝ) :=
    ∀ j i, Adj j i → B.first ≤ i → Starcash Z K D (W.betaEntry j) j i (g j i) (a j i) (E j i)

variable {D} {W : Delays T}

/-- BEFORE any Bar. boost W to pay charts, preserving Ringing.
Use also with Scheduling.Regime.carry on the same Boost. -/
lemma issue_cosmos (hZ : LocalRatio Z) (W : Delays T) (g : ℕ → ℕ → ℝ) (h : Ringing K g W) :
    ∃ X : Delays T, Boost W X ∧ Ringing K g X ∧ ∃ a E : ℕ → ℕ → ℝ, Cosmos Z K X g a E := by
  have he (j i : ℕ) : ∃ x a E : ℝ, Adj j i → B.first ≤ i → Starcash Z K D x j i (g j i) a E := by
    by_cases he : Adj j i ∧ B.first ≤ i
    · have hw := (h.receipts _ _ he.1.1 he.1.2 he.2).pos
      obtain ⟨x,a,E,hC⟩ := buying Z K D hZ (j:=j) (i:=i) _ hw (B.cut.trans (he.2.trans he.1.1))
      exact ⟨x,a,E,fun _ _ => hC⟩
    exact ⟨0,0,0,fun u v => False.elim (he ⟨u,v⟩)⟩
  choose x a E hX using he
  let X : Delays T := { W with betaEntry := fun j => max (W.betaEntry j) (max (x j j) (x j (j-1))) }
  have hB : Boost W X := ⟨fun i => le_max_left ..,le_rfl,le_rfl,le_rfl⟩
  refine ⟨X,hB,Bid.recheck hB.beta h,a,E,?_⟩
  intro j i ha hf
  obtain ⟨hi,hp,hx⟩ := hX j i ha hf
  refine ⟨hi,hp,fun b hv => hx b ((le_max_of_le_right ?_).trans hv)⟩
  rcases ha.cases_back with e|e <;> subst i
  · exact le_max_left ..
  exact le_max_right ..

section client
variable {s : Supply.Sheet G} {D : Rolls s} {Θ : Protection D} {W : Supply.Delays Θ} {Y : Bar W} {I : Wait Y} {P : PostCost D}
    {Z K} (F : Directed G I Z K P) {g a E : ℕ → ℕ → ℝ}
private lemma threshold (m n : ℕ) : fiery G (F.a.clock.hatBeta m) ((F.a.clock.op m n).patch.L) = F.a.clock.threshold (m+1) := by
  have hl : F.a.clock.hatBeta (m+1)=betaF G (F.a.clock.hatBeta m) ((F.a.clock.op m n).patch.L) := by
    unfold Calendar.hatBeta betaF
    rw [Schedule.scale_succ]; change _ = _ + _ * Real.log (F.a.S.block m).val; unfold Levels.S; ring
  change temp _ = temp _; rw [hl]

/-- Downstream actual sector application (as input to density transfer
consumer). Purchase even quantitative chart prices here without J-algorithm
or Gaussian Hessian inputs. Does NOT apply charge to Gaussian multipliers
after changing prerequisites: `PortionCost.cost` read on intact slices.
All displayed integrals and *each in the push identity* licensed. -/
theorem committed (hW : Ringing K g W) (bill : Cosmos Z K W g a E) (N m p : ℕ) (hn : m<N)
    (R : Rep G (F.a.S.side (m+1) p)) (hR : Lives F.bake N (m+1) p R) (hb : R.beta∈band F.a (m+1)) :
    let j := F.a.clock.J (m+1); let i:=F.a.clock.J m
    let S := F.a.clock.op m p; let U := ships F N m p; let x := F.a.clock.hatBeta m
    let w := g j i; let d := a j i * F.a.clock.threshold (m+1)
    let v H A k V := fog A H U x V k
    let l H A k V q := meanLog A H U x V k q d
    0 < w ∧ 0 < d ∧ 2*d < firstRadius G ∧ 4*d < Z.radius ∧ 0 < E j i ∧
      (∀ t : G.Color, ‖t‖ ≤ 4*d → |Real.log (Z.J t)| ≤ E j i*‖t‖^2) ∧
    0 < R.beta ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ (D : Allocation G S x w) (H : Forest S.ratio) (q : Chi),
    Presented.PortionCost D H U κ R ∧
      (∀ (A : Stores S) (k : S.Choices) (V : Config G _),
        Admitted A H x V k Z D d ∧ (A.flags=RG.flags (temp x) V → (v H A k V).PosDef ∧
          (Rows.gram U x V k (shots S x) A H).PosDef ∧ (∃ B, 0<B ∧ Authorized A V H x B)) ∧
        Licenses U x V k A R (shots S x) H D q Z d (v H A k V) (l H A k V q)) ∧
      ∀ (V : Config G _),S.push R.beta R.eval V = ∑ A : Stores S, sieve U R.beta x V * ∑ k,
        prefactor S G R.beta*Z.scale ^ Fintype.card (Active A x H) * chartCost (v H A k V) (coupling R.beta)*
          ∫ y, (∫ z, dyed U x V k A R (shots S x) H D q Z d (v H A k V) (l H A k V q) y z ∂cloud (v H A k V))
            ∂piHaar G (Frozen A x H) := by
  intro j i S U x w d v l
  have hadj : Adj j i := Deployment.adj F.a _
  have hg : s.first ≤ i := by rw [← F.valid.firstZero]; exact F.a.fits.mono (Nat.zero_le m)
  obtain ⟨hw,κ,hκ,h⟩ := Consumer.bought F g hW j i hg hadj.1 hadj.2
  obtain ⟨hi,ht,hh⟩ := bill j i hadj hg
  obtain ⟨he,hr,hZ,hX,hB⟩ := hh x (F.valid.pays m)
  have hL : S.patch.L = D.L j := (F.a.fits.sameFactor _).symm.trans (congr_fun F.valid.lengths _)
  have hsize : 100 * (1+radiusB x) ≤ (F.a.S.side m p).val := by rw [add_comm]; exact F.a.fits.sizeT m p
  have hx := proceeds F N m p hn
  obtain ⟨hl,hf,hG⟩ := hB _ _ S rfl hL hsize U hx
  have hd : fiery G x (D.L j)=F.a.clock.threshold (m+1) := by rw [← hL]; exact threshold F ..
  rw [hd] at he hr hZ hX hG
  have hn' := F.a.fits.delayed (m+1)
  have hβ := hb.1
  have hβ' : 0 < R.beta := by unfold band at hβ; linarith
  obtain ⟨-, -, hC,hF⟩ := h N m p hn rfl rfl
  refine ⟨hw,he,hr,hZ,ht,hX,hβ',κ,hκ,fun D H q => ?_⟩
  have hh := hF R hR hb H D
  have hy A k V : Admitted A H x V k Z D d ∧ (A.flags=RG.flags (temp x) V → (v H A k V).PosDef ∧ (Rows.gram U x V k (shots S x) A H).PosDef ∧ (∃ B, 0<B ∧ Authorized A V H x B)) ∧ Licenses U x V k A R (shots S x) H D q Z d (v H A k V) (l H A k V q) := by
    obtain ⟨ha,hP⟩ := hG A H D k V q
    refine ⟨ha,fun hw => ?_,?_⟩
    · exact ⟨(hP hw _ hβ').1.nativePos,(hP hw _ hβ').2⟩
    by_cases hz : A.flags=RG.flags (temp x) V
    · exact authorized_change U x V k A R _ H D q Z d (hP hz R.beta hβ').1 hR.valid hx
    exact displaced_wrong U A H x V k Z D q R _ _ _ hz
  refine ⟨hh,hy,fun V => ?_⟩
  rw [hh.total V]
  refine Finset.sum_congr rfl fun A _ => ?_
  unfold cutEntry Allocation.column tagTotal
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (hy A k V).2.2.result
end client
end YM.Next.SectorChange
