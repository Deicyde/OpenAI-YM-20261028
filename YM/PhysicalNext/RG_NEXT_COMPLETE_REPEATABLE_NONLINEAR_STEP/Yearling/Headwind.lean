import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Carpets

/-!
 # Upgrade sched grid (ask pre-H floor) and execute INcomes on full-beta trajectory.
 Use arbitrary Embrasure including Fresh, canonical masks. Still need budget regroup &
 cancellation. Origins not used to assert availability of this input.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Yearling
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}
section calls
variable {s : Sheet G} {K : MapPrices} {X : Targets s K} {D : Rolls s} {Θ : Protection D} {p : Expenses X} {u : Return.Wages} {l : ℕ→ℝ} {P : Teller G}

def Stargaze (Q : ConnectedActivityE6.Target G P) (L:Side) (W : ℝ) (o : Target.Order G W) (μ x : ℝ) (i:ℕ) := ∃ v:ℝ,∀ (c f:Side) (S:StepData c f) (T:Tube G S), Works P L x S T→ Stamp T → ∀ (R: RG.Rep G f) (C:ℝ) (H: Cash W x μ L Q o C T R),Nonempty (Year H i v Chi.canonical)
def Hood (s : Sheet G) (K : MapPrices) (X : Targets s K) (M : ℕ → ℕ) := ∀ j i, StepStages j i → ∀ L:Side,M j ≤ L.val→ ∀ W (o : Target.Order G W) μ, 0<W→0<μ→∀ᶠ x in atTop, Stargaze (X j i) L W o μ x (s.profile i).order
lemma herald (Q : ConnectedActivityE6.Target G P) (X : Target.Expense Q) : ∃ M:ℕ,∀ L:Side,M≤L.val→ ∀ W (o:Target.Order G W) μ (i:ℕ), 0<W→0<μ→∀ᶠ x in atTop, Stargaze Q L W o μ x i := by
  obtain ⟨K,H⟩:= Yearling.sterling P Q (by linarith [X.price,X.worth,X.first,X.second])
  refine ⟨K,fun L hL W o μ i hW hm=>?_⟩; by_cases he:∃ D:Patch,D.Branches P.bind G∧D.L=L∧ D.J=P.j
  swap; · exact Eventually.of_forall fun x=> ⟨1,fun c f S T h =>False.elim (he ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩)⟩
  obtain ⟨D,hd,hF,hX⟩:=he
  filter_upwards [H L hL D hd i Chi.canonical W μ hW hm o ] with x hx
  obtain ⟨v,hv,h⟩:=hx; exact ⟨v,fun c f S T hw=>h c f S T (hw.patch hF hX)⟩
theorem batten (X : Targets s K) (p : Expenses X) : ∃ M, Yearling.Hood s K X M:= by choose b hb using fun j i=> herald (X j i) (p j i); exact ⟨fromMax b,fun j i hj L h W o μ=> hb j i L ((le_fromMax b hj).trans h) W o μ _⟩
variable (R : Register D p u l)
def Acre (V : Delays Θ) := ∀ j x,V.betaEntry j≤ x →∀ i,StepStages j i→ Stargaze (X j i) (D.L j) (u j i) (R.o j i) (R.μ j i) x (s.profile i).order
lemma brine {l} (h : Yearling.Hood s K X l) (he : ∀ j,l j ≤ (D.L j).val) (V : Delays Θ) : ∃ W : Delays Θ,DelayLe V W∧ ∀ Y:Delays Θ, DelayLe W Y → Yearling.Acre R Y:= by
  obtain ⟨x,-,hx,H⟩:= collect_upper V.betaEntry _ fun j=> eventually_transitions j _ _ (fun i hi=> h j i hi (D.L j) (he j) _ (R.o j i) _ (R.consumes j i hi).1 (R.consumes j i hi).2.1)
  exact ⟨{V with betaEntry:=x},⟨hx,le_rfl,le_rfl,le_rfl⟩,fun _ hz j x hx i hi=> H j x ((hz.beta _).trans hx) i hi⟩
end calls
variable {M : Metals G} {D : Rolls M.p} {U : Alloy M D} {bt : Baton G} {v w t : Return.Wages}
    {L : Targets M.p M.K} {p : ℕ→ℕ→JointLoad.Heir.Record} {V : Programs M.p} {F : ℕ→ℕ→Postage} {S : Time.Scouts (F:=F)} {r : ℕ→ℕ→ℕ} {b : ℕ→ℕ→Booth} {E : Expenses L} {H : ℕ→ℕ→Cafe} {Q : ℕ→ℕ→Clockwork.Menu} {a : ℕ→ℝ} {Y : Register D E w a}
    {J : ℕ→ℕ→Folio.Aux} {c c₁ c₂ : ℝ} {E₀ : ℕ→ℕ→Next.Scheduling.Exchange} {η : ℕ→ℝ} {q : UVNext.CouplingReset.ResetPrices}
    (h : Touring (C:=V) (B:=H) U bt v t r b Q p J Y S c E₀ q η)
local notation "X" => U.B
local notation "W" => U.delay
variable {N m n : ℕ} {R : ℝ → RG.Rep G (U.B.a.S.side (m+1) n)} {θ : Set ℝ} {y : ℝ}
variable (T : Embrasure (N:=N) (Y:=Y) R θ y)
variable (hL : ∀ x∈θ,Lives U.B.bake N (m+1) n (R x) ∧ (R x).beta∈band U.B.a (m+1)) (hc : Curve (U.B.a.budget (m+1)) R θ)
   (hy : Acre Y U.delay) (he : Opera.Treble U.delay) (hm:m<N)
include h hm hy he hL hc
lemma hearthcast : Compared T.doors (U.B.a.budget m) T.fullSong θ:= by
  let D:= T.doors; let B:= U.B.a; let T':= ships X N m n; let x:= B.clock.hatBeta m; let i:= B.clock.J (m+1); let j:=B.clock.J m; let o:=B.budget m
  have hi := step_paid B m
  have hv := h.machine.passes hm hL
  let P:=M.p.profile j
  have hB := params_eq U.B.valid m
  have hn : o.order≤P.order := le_of_eq (congr_arg RG.Stage.order hB)
  have hp : preExponent o / o.B ≤ (B.params m).width/2:= by
    have hh:= he _ _ (U.B.valid.pays m) _ hi
    rw [show preExponent o=P.supportExponent+3 from congr_arg (fun t:RG.Stage=> t.supportExponent+3) hB, show B.params m=P from hB]; exact hh
  have hQ := T.base.laws.data.funds
  let l:= E i j
  have hk (i:θ):Cash.Renewed l.degrees l.earn l.one l.two (T.houses i):= T.honors i
  obtain ⟨v,hS⟩:= hy i x (U.B.valid.pays m) j hi; let V (i:θ) := (hS _ _ _ T' hQ (protocol X hm h.full) _ _ (T.houses i)).some
  apply Yearling.compared o rfl hn (show T'.down.Bounds T'.low _ _ _ from U.B.support.cap N m hm.le) hv.1.decent hp T.houses hk V T.base T.sister (U.B.kin.alpha N m) T.agrees (Beam.dashboard T.base) (Beam.see _ ) T.fullSong ?_ _ (fun i hi=> (hL i hi).1.point) hc fun i j=> ?_
  · intro i; unfold Embrasure.fullSong; rw [Embrasure.click _ _ i.2]
  exact ⟨((hL _ i.2).1.clip).trans (hL _ j.2).1.clip.symm,((hL _ i.2).1.path).trans (hL _ j.2).1.path.symm⟩
end YM.PhysicalNext.Repeat.Yearling
