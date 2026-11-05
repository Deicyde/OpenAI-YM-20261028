import YM.Further.LOCAL_LOG_JETS.Series
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.WardExports
import YM.MergeProof.Temper
/-! Occupancy (global) and restoration (permitted modes). Generic multiple path. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac Menu
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V : Type} [Fintype V][DecidableEq V] {B:Census V} {G:Gauge}{f c:Side}
open GridApprox.Nil Local Extra.Trajectories Source Extra.Multi
variable (A:History G) (r:ℕ→ℕ)(δ u:ℕ→ℝ)(D:∀ N p m:ℕ,m<N→GaugeDoor (A.rep N p (m+1)) (A.rep N p m))
set_option quotPrecheck false
local notation "K"=>A.levels
local notation "P"=>A.levels.budget
local notation "Δ"=> (fun k=> (A.levels.budget k).supportExponent-3)
structure Moonlit : Prop where
    days (N p k:ℕ)(hk:k<N) : ∃ y w, Volant (A.levels.clock.op k p) (D N p k hk) (r k) ((A.levels.budget (k+1)).supportExponent-4) y ((A.levels.budget k).supportExponent+1/2) ((A.levels.budget k).supportExponent+1) 1 w ∧ Duty A r k (δ k) y w
    endow (k:ℕ) : let Q:= P k; 0 ≤ u k ∧ 0 ≤ Q.supportExponent-3 ∧ let C:ℝ:= A.levels.clock.forcedAllowance k + r k*siteFactor Q.B*u k
                                ((Q.B + Q.B + 1:ℕ):ℝ)^4*C ≤ 3 ∧ Real.exp C-1 ≤ 1

variable (p N k:ℕ) (o:∀ m:ℕ,V → Site (A.S.side m p))(w:ℕ → V→ℝ)
local notation "S"=> A.S
structure Matchup (B:Census V):Prop where
    pos (i) : k ≤ i → i≤ N → ∀ j, 0 < w i j
    occ i : k ≤ i → i ≤ N → Occupancy (o i) (r i)
    next i : k ≤ i → i<N → Occupancy (o (i+1)) (r i)
    pins i : k ≤ i → i<N → (A.levels.clock.op i p).ratio.parent ∘ o (i+1)=o i
    runs i : k ≤ i → i<N → Repegs (o i) (P i).B (fun j=> δ i*w (i+1) j) (w i) (1/2) 1 B
local notation "R"=> (A.rep N p)
local notation "C"=> fun i=> Config G (A.S.side i p)
-- single F initial pinned and physical coin. We keep K witnesses existential. tally invoice independent of mode-algebra. 
variable (f:∀ m:ℕ,V  → Config G (A.S.side m p)→ℂ)(g:∀ m:ℕ,V→ℕ → Config G (A.S.side m p)→ℂ)(F: V → Config G (A.S.side N p)→ℂ)
def manifest (m:ℕ)(i:V):= coin (A.rep N p m) (f m i) (g m i)
def tapes (g:∀ m:ℕ,V→ℕ → Config G (A.S.side m p)→ℂ)(m:ℕ)(i:V):= profile (A.rep N p m).activities (g m i)
local notation "M"=> manifest A p N f g
local notation "T"=> tapes A p N g
structure Nectar (i:V) : Prop where
    stocked m : k ≤ m → m≤N→ Dominated (g m i)
    writes U : ((R N).eval U:ℂ)*F i U= M N i U
    patent : ∃ (z : MergeProof.Response G (A.S.side N p)) (a:ℝ), Attainment (R N).p (o N i) z a ∧ w N i*a ≤ u N ∧ hook (R N).activities (R N).p.threshold z=T N i
    sways m : k ≤ m →∀ hN:m<N,∃ (ψ:Set PhysicalNext.Repeat.Lotus.Wing) (v:ℂ)(s t:ℝ), ψ.Finite∧ 2*w (m+1) i*s ≤ 1 ∧ w (m+1) i*t ≤ 1 ∧ Tale ψ (o (m+1) i) (o m i) 1 (f (m+1) i) (T (m+1) i) (T m i) v s t (D N p m hN)
    feeds m : k ≤ m → m<N → M m i= (A.levels.clock.op m p).push ((R (m+1)).beta) (M (m+1) i)

variable {A}
lemma cloth {g:V→MergeProof.Response G c}{r:V→ℝ}{s:V→ℝ}{u:ℝ}{o:V→Site c}{Pt:BudgetPoint}(h':∀ i,Attainment Pt (o i) (g i) (s i))(h:∀ i,r i*s i ≤ u)(hp:∀ i,0 ≤ r i):Garnish Pt o g r Pt.supportExponent u:=by
    refine ⟨fun i=>(h' i).shaped,fun i=>(h' i).marked,fun i=>?_⟩
    obtain ⟨w,hV,hw⟩:= (h' i).toll; refine ⟨w,hw, le_trans ?_ (h i)⟩
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hV.2.2 (hp i)); rw [tsum_fintype, mul_sum]; apply sum_le_sum; intro j _; rw [mul_left_comm]; unfold reservedMass; gcongr
    all_goals first | exact hp i | exact (hw j).1 | linarith
variable {n:Side}
omit [Fintype V] in
lemma push_get {Ss:StepData c n}{φ : Config G n→Poly B}{x:ℝ}(h:Ss.IsKernel x G)(hp: Integrable φ (prior G _)) (s:B.Mode): (fun U=>(Ss.push x φ U).part s)= Ss.push x (fun U=> (φ U).part s):=by
    let L:= (Poly.get s).restrictScalars ℝ; funext U; unfold StepData.push; have hx:= L.integral_comp_comm (StepData.push_slice h U φ hp); simp_rw [L.map_smul] at hx; exact hx.symm
end YM.MergeProof.Accent
