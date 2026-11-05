import YM.RemainderComparison.Chron.Public
import YM.RemainderComparison.Beacon.Physical
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Hymnal
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Lantern Slide
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open Height Input Org Supply Pane Push.PriceCompiler Bid Legato Stagehands
open Aux Funk Herbal Cadenza Chron
open Further.PhysicalPeriodLimitF933 Further.PhysicalPeriodLimitF933.Mural RG.Shoot Opera Roost Roof
open JointLoad JointLoad.Heir
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A:Alloy X D} (F:Factor A)
variable {N m n :ℕ}
-- ALL output geometry R certificates apply
local notation "i" => A.B.a.clock.J m
local notation "j" => A.B.a.clock.J (m+1)
local notation "K₀" => F.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)
local notation "p" => A.B.a.clock.op m n
local notation "G'" => ships A.B N m n
abbrev slot (A:Alloy X D) (m:ℕ) := Mural.sheet X.p D (A.B.a.clock.adm (m+1))
local notation "P₀" => slot A m
local notation "σ" => F.span j i
local notation "Z" => F.prices j i
local notation "Y" => F.shape.o j i
local notation "B" => A.B.a.budget m
local notation "V" => A.B.a.budget (m+1)
local notation "δ" => A.B.a.clock.hatBeta m

lemma patchA : (p).patch = P₀:=by
   cases e : (p).patch with
   | mk k d hm hf ho=>
     have h : k=D.L j:= by rw [← show (Patch.mk k d hm hf ho).L=k from rfl, ← e]; exact PriceCompiler.block_eq A.B.valid m
     have hd : d=A.B.a.clock.J (m+1):=by rw [← show (Patch.mk k d hm hf ho).J=d from rfl,← e]; rfl
     subst k d; rfl

-- forecast aptitude from actual stock.Stamp
lemma orient (A:Alloy X D) (m:ℕ) : (slot A m).Branches (X.p.kernel) G:= by
    rw [← patchA (n:=0),← A.B.valid.kernel]; exact (A.B.a.blocks m 0).branches
variable {T: Contemple G}
local notation "W'"=> Stagehands.atlas F T
local notation "L" => D.L (A.B.a.clock.J (m+1))
 set_option quotPrecheck false
local notation "E'"=> X.p.profile (A.B.a.clock.J m)
variable (y:Book (Stagehands.atlas F T))
variable (hG:Pillar (Stagehands.atlas F T) F.prices F.span F.recordP F.shape T A.delay y)
variable (w : Fin ((Stagehands.atlas F T).count (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)))
local notation "x" => (W').slots j i w
local notation "t"=> (x).scope
local notation "r" => Glint.award (x) E' (Glint.partition E' (K₀).exp)
local notation "D'" => y j i w

include hG
lemma pref : (r).Heart E' (K₀).exp ∧ 0<(D').d∧ PaintSupply G (r).wind (D').Z ∧ Allot (K₀) (Y) (P₀) (r) ((x).propAim) ((x).scope) (E') (D') (μ:= F.shape.μ j i) X.p.kernel (X.p.profile j) (Z) (F.recordP j i) Chi.canonical (F.span j i) (x).η_goal (x).limit (x).ξ (A.delay.betaEntry j) :=
    let hp:= hG.buys _ _ w (step_paid A.B.a m) (first_le A.B.valid m) (A.B.a.clock.adm (m+1)) (orient A m)
    ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1⟩
-- Same estimates authorized on natural rays (ticket ownership).
lemma leased : (x).books.extra D' δ:= (hG.buys _ _ w (step_paid A.B.a m) (first_le A.B.valid m) (A.B.a.clock.adm (m+1)) (orient A m)).2.2.2.2 _ (A.B.valid.pays m)
lemma billed (n:ℕ) : ((W').slots j i w).scope.Tiled δ (A.B.a.S.side m n):= by
    apply hG.brings _ _ _ (step_paid A.B.a m) (first_le A.B.valid m) _ (A.B.valid.pays m) _
    refine le_trans (Nat.mul_le_mul_left (A.delay.shells j) ?_) (A.B.valid.volume m n); exact Nat.pow_le_pow_left (show 1+radiusB (δ) ≤ _ from Nat.le_add_right ..) _
lemma quota : ∃ g:ℕ→ℕ→ℝ,∀ m:ℕ,
     let M:=(A.B.a.budget m); let i' := A.B.a.clock.J m; let j' := A.B.a.clock.J (m+1); let hy₁:=A.B.a.budget (m+1); let P:=X.p.profile i'; let P':=X.p.profile j'
     Release.Quotation (F.prices j' i') M.power (F.span j' i') hy₁.supportExponent (squash P) (g j' i')∧ Release.accepts (F.span j' i') hy₁.supportExponent (squash P) (D.L j')∧ g j' i'/(D.L j').val ≤ T.hearth j' i' P' P:=by
    obtain ⟨u,C,hp,h⟩:= hG.expenses
    refine ⟨C,?_⟩; intro m Q i' j' V' P P'
    have ht : Q.power=P.power:=congr_arg RG.Stage.power (params_eq A.B.valid m)
    have hv : V'.supportExponent=P'.supportExponent:= congr_arg RG.Stage.supportExponent (params_eq A.B.valid _)
    rw [ht,hv]; exact ⟨(hp j' i').1,((hp j' i').2 (step_paid A.B.a m) (D.L j') (h _)).2.2⟩

lemma pitches (m:ℕ) : Lyric.radiusCost (F.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (slot A m).L (A.B.a.budget (m+1)).supportExponent:= by
    obtain ⟨u,C,hp,h⟩:= hG.expenses; rw [show (A.B.a.budget (m+1)).supportExponent=(X.p.profile (A.B.a.clock.J (m+1))).supportExponent from congr_arg RG.Stage.supportExponent (params_eq A.B.valid (m+1))] -- review target reducible
    exact ((hp _ _).2 (step_paid A.B.a m) (D.L _) (h _)).2.1
-- Min active-tools pilots. `Panel` uses exact same Β scale and Rep two radii. Faces.
omit hG
variable {R : RG.Rep G (A.B.a.S.side (m+1) n)} (hm:m<N)(hl:Lives A.B.bake N (m+1) n R)(hβ:R.beta∈band A.B.a (m+1))
include hm hl hβ
lemma budgets : (Plays (Z) (F.recordP j i) (B) R.p (asks A m) (G') δ ∧ Lute.Plented (Z) (F.recordP j i) (B) R.p L σ δ (gStep R.beta)) ∧ (K₀).halo+5 ≤ σ ∧ Temper (B) (E') δ G (P₀).L:= by
    let H:=F.pledging.conducts
    have hz:= (Psalm.Stage.directed H.hearing A.B hm hβ hl (fun m' h'=>H.full _ _ _ (by simp at h'; omega))).1.enabled
    have he : (V).threshold=Pressure.fiery G δ L:= congr_arg Pressure.temp (PriceCompiler.beta_eq A.B.valid m)
    have hp:= params_eq A.B.valid m
    refine ⟨⟨hl.point.symm ▸ hz.make, hl.point.symm ▸ (PriceCompiler.block_eq A.B.valid m) ▸ (hz.clocks R.beta hβ).2⟩, F.pledging.agenda _ _ (step_paid A.B.a m)|>.2.2, ?_⟩
    exact ⟨rfl,rfl,congr_arg RG.Stage.power hp,congr_arg RG.Stage.order hp,congr_arg RG.Stage.supportExponent hp,he ▸ hz.make.rehearsed.tensions.coarse⟩
end YM.RemainderComparison.Hymnal
