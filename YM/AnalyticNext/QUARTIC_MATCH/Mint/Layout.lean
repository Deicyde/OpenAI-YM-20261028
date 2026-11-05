import YM.AnalyticNext.QUARTIC_MATCH.Local.Direction
import YM.AnalyticNext.QUARTIC_MATCH.Pre.Trial
import YM.AnalyticNext.QUARTIC_MATCH.Range
import YM.Progress.JOINT_CALENDAR.Kinetics
import YM.Progress.STATIONARY_SCENES.Classical
import YM.Push.PRICE_COMPILER.Authors




/-!
# Pre-L production -- booking original operations, not the extensions

Orders on the Answer witnessing the actual path invoice. Keep *all* the
periods; each of the auxiliary `Series` choices automatically conforms on
the genuine schedule's tags at every call. Width for incoming `row` label
transport (ell) and access price for each actual operation, separate from
linear metric/spool, in general. Reserve cubic outgoing width BEFORE issuing
quartic and keep even at same-stage iteration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Mint
open Filter Function Lattice Laurent Matrix RG Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Next YM.Next.Free Work.F08 Tree Joint BoxChain Mail Analyzers
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

section probes
variable {G : Gauge} {a : Levels G} {m N : ℕ} {H : Horizon a} {K : MapPrices}

def AdmitsMesh (a : Levels G) (m : ℕ) := ∀ i,Larger (G:=G) (a.clock.op m i)
abbrev turf (a : Levels G) (m : ℕ) := (a.clock.op m 0).patch
lemma plays (a : Levels G) (m : ℕ) : (turf a m).Branches a.clock.kernel G := (a.blocks m 0).branches
lemma tends (a : Levels G) (m : ℕ) : Tendsto (fun i => (a.S.side m i).val) atTop atTop :=
  tendsto_atTop_mono (fun _ => Nat.le_mul_of_pos_right _ (a.S.denominator m).property) a.S.period_strict.tendsto_atTop
lemma threshold_paid (h : AdmitsMesh a m) (i : ℕ) : Analyzers.allowanceSide (turf a m) ≤ (a.S.side m i).val := by
  let P := turf a m; let u := P.L; let S := a.clock.op m i
  have ht : 100*Pressure.macroR P=Analyzers.allowanceSide P * P.L.val := by
    unfold allowanceSide Pressure.macroR Patch.radius; ring
  have hx := (h i).2.1; rw [S.sizes] at hx; exact Nat.le_of_mul_le_mul_right (ht ▸ hx) P.L.property

lemma visit (hf : H.Suffices K) (he : m<N) (c : Side) :
    let U := (H.towers N m).A0; let B := turf a m; let j := B.J; let S := Sheets.stepAt B a.clock.kernel c
    Local.Evoke.motion S U (K.α j) (K.Ω j) ∧ Inputs S (installed S.ratio U) ((H.H N (m+1)).metric.acts (c*B.L)) ((H.H N m).metric.acts c) := by
  intro U B j S
  have h c' : Local.Evoke.motion (Sheets.stepAt B a.clock.kernel c') U (K.α j) (K.Ω j) := by
    intro l hl
    apply (hf.costs N m he).2.2.2 l _ |>.1
    have hp := a.clock.adm (m+1); omega
  have hh : Whole U := ⟨_,_,K.alpha_pos _, h c [] (by simp)⟩
  have hx : ∀ i j,j ≤ N → j=i → Whole (H.H N i).metric := by
    rintro i _ hi rfl; exact ⟨_,_,K.alpha_pos _,(hf.rows N _ hi).2.1⟩
  refine ⟨h c, Pre.Rows.across (a.clock.op m) B a.clock.kernel U _ _ (tends a m) (hx _ _ he rfl) (hx _ _ he.le rfl) hh
    (fun _ => rfl) (fun _ => rfl) (fun i => ?_) c⟩
  exact (hf.crossings N m i he).trial

variable {W R : PathData G} {x τ Λ b η : ℝ}
variable (A : Answer H N m W x)

def UpTo (k : ℕ) (R : PathData G) :=
    ∀ (i) (U : Forest (a.clock.op m i).ratio) (t : (a.clock.op m i).Choices) (j : ℕ), j ≤ k →
      SameJet j (A.classicalValue i U t) (Residual.baseAt (a.params m).clip R)



lemma upward (h : Funded H N (m+1) W) (hp : AdmitsMesh a m) {Y : Analyzers.Series (turf a m) a.clock.kernel G (H.H N (m+1)) (a.params (m+1)).clip W b}
    {i j} (hh : UpTo A j R) (k : ℕ) (he : k<j+1) : iteratedFDeriv ℝ k (Y.canonical (a.S.side m i)) 0=iteratedFDeriv ℝ k (Residual.baseAt (c:=a.S.side m i) (a.params m).clip R) 0 := by
  let F := exampleTree (a.clock.op m i); let t : (a.clock.op m i).Choices := Classical.arbitrary _
  have hz := Y.canonical_value h.bound _ (a.clock.op m i) rfl rfl F t (A.station i F) (A.critical i F) (hp i)
  exact ((hz.iteratedFDeriv ℝ k).eq_of_nhds).trans (hh i F t k (by omega)).2.2
lemma descend {j} (h : Funded H N (m+1) W) (hp : AdmitsMesh a m) {Y : Analyzers.Series (turf a m) a.clock.kernel G (H.H N (m+1)) (a.params (m+1)).clip W b}
    (H : ∀ i k : ℕ,k≤j → SameJet k (Y.canonical (a.S.side m i)) (Residual.baseAt (a.params m).clip R)) : UpTo A j R := by
  intro i F t k he
  have hz := Y.canonical_value h.bound _ (a.clock.op m i) rfl rfl F t (A.station i F) (A.critical i F) (hp i)
  obtain ⟨h₀,h₁,h₂⟩ := H i k he
  exact ⟨(A.classical_value i F t).2.2,h₁, ((hz.iteratedFDeriv ℝ k).eq_of_nhds).symm.trans h₂⟩

lemma purchased (h : Funded H N (m+1) W) (hf : H.Suffices K) (hw : Progress.Joint.Swears H) (he : m<N) :
    ∃ b, Nonempty (Analyzers.Series (turf a m) a.clock.kernel G (H.H N (m+1)) (a.params (m+1)).clip W b) := by
  obtain ⟨b,-,hb⟩ := serves _ _ _ (K.eta_pos (a.clock.J (m+1))) (plays a m)
  exact ⟨b,hb _ _ W _ _ _ _ h.bound h.ties (fun c => hw _ _ _ he) (hf.all _ _ he)⟩
end probes
end YM.AnalyticNext.QuarticMatch.Mint
