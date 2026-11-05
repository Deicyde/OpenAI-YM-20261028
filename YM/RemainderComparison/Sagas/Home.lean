import YM.RemainderComparison.Sagas.Rind
/-! Sonorous.Space. Use χ support adjacency.Blueproof stamps.Kernel MUST come in
cover units across roots, not merged-mode counts. Allows combining long tags
before costing on authenticated P.Posts.Use in AUX standing BOTH on pulses and
in inherited/auth relief. -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Sagas
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open Height Input Org Supply Pane Push.PriceCompiler ThroughLaunch Bid Planned.JetPort
open YM.RemainderComparison.Aux Portal Herbal
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{c f:Side}{L:Side}{α:Type*}{ι J:Type}
variable (p:BudgetPoint) (β:ℝ)
namespace Packet
variable {αP dθ t b η x B:ℝ}{n k r m:ℕ}
open Time WickReps
variable (P:J→ Packet G f α)
variable (Q: Manor G f ι α J)(R:ι→Support f)
structure MCC (κ δ σ B:ℝ)(k n:ℕ)(ℓ:ℕ) : Prop where
   cost : Ac.Hit Q.halls p.B (fun i=>(P i).weight*Real.exp (σ*(P i).length)) 0 B -- remove
   quotes i: (P i).postage=Q.rooms i ∧ (∀ a:α, Q.solvent a i=(P i).send β a) ∧ Manor.Sees Q p R i
   high i: n ≤ (P i).grade ∧ (P i).rank≤ k
   shape i : (coverNumber p.B (Q.halls i):ℝ) ≤ κ+δ*(P i).length
   holdings i : Q.halls i⊆ neighbors (ℓ*(p.B+(P i).length)) (P i).postage.site
-- Local Mutation α.Resource all.Query.Math.World.
set_option quotPrecheck false
local notation "d'" => p.power * p.order
local notation "pX"=> gStep β
variable (h:MCC p β P Q R αP dθ η B k n r)
variable (FX:Stage)(hP:Same FX p)(hβ:0 < β)(he:gStep β ≤1)(hb:0≤b){ξ:ℝ}(ht:0<ξ)(hξ:t + b*dθ+2*ξ ≤ η)
local notation "μW"=> music G FX ξ b αP n k β p.threshold
local notation "H₀"=> momentPrice d' ξ
local notation "W₀"=> 1+(r:ℝ)*(p.B:ℝ)
include h hβ hP he hb ht hξ
-- model may arrive already ROOT SUP instead of anchored, to be consumed e.g. bills from scale compiler.T stage.N. no AUTH.W mismatch. Maps choose no clocks.
lemma yields : Breeze.Sonorous p Q (fun i=>(P i).length) Set.univ R b t ((H₀* (W₀)^d' * μW)*B):=by
    let a:= H₀; let w:= W₀; have ha:0≤a:=(momentPrice_pos _ ht).le; have hw:1≤w:= le_add_of_nonneg_right (by positivity)
    let F i:=(P i).eats β p; let o i:=(P i).postage.site; let L i:ℝ:=(P i).length
    let f i:= (w*(1+L i))^d'*F i; have hz i : 0 ≤F i:= fee p _ β; have hc:0≤ μW :=by unfold music; have ht:= (Fare.gS _ hβ).1; have he:= p.threshold_pos; have hv:= tolls G FX ξ k; positivity -- F shadow
    have hv i: 1 ≤ w*(1+L i):= one_le_mul_of_one_le_of_one_le hw (le_add_of_nonneg_right (Nat.cast_nonneg _)); have hx i: 0 ≤ f i:= mul_nonneg (pow_nonneg (zero_le_one.trans (hv _)) _) (hz i)
    refine ⟨f,hx,fun i _=>⟨(h.quotes i).2.2,?_⟩,fun x=>?_⟩
    · intro a y hy; rw [(h.quotes i).2.1 a]; have he : Q.halls i=(P i).postage.support:=by rw [(h.quotes i).1]; rfl
      obtain ⟨hi,hp'⟩:= Packet.solo β (P i) p a hβ -- give
      have hm := (neighbors_mem ..).mp (h.holdings i hy); let u:=(P i).length; let A:= w*(1+L i)
      have hg : 1+(separation (o i) y:ℝ) ≤ A :=by
         have h': (separation ((P i).postage.site) y:ℝ) ≤ r*((p.B:ℝ)+ u):=by exact_mod_cast hm
         have H:= p.B_pos; have hh:1 ≤ (p.B:ℝ):=by exact_mod_cast H
         unfold o A w L u at *; nlinarith only [h',mul_le_mul_of_nonneg_left hh (mul_nonneg (Nat.cast_nonneg (α:=ℝ) r) (Nat.cast_nonneg (α:=ℝ) (P i).length)), Nat.cast_nonneg (α:=ℝ) (P i).length]
      rw [he]; apply (sup_real hi).1; refine ⟨hx i,fun U h t ht hr=>?_⟩; exact (Extra.Multi.Germs.relocated_bound hg ((sup_real hi).2 hp') h t ht hr).trans ((mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (one_le_pow₀ (hv i)) ht) (hz i)).trans_eq (by unfold f; rw [pow_mul])) -- order
    apply budget_mono (Cost.scale (h.cost x) (a*w^d'* μW) (by positivity)) ?_ ?_
    · intro i; split; exact mul_nonneg (mul_nonneg (hx _) (Real.exp_pos _).le) (Real.exp_pos _).le; exact le_rfl
    intro i; split; swap; · simp
    next hQ=>
      unfold f; rw [mul_assoc,mul_assoc,mul_pow]; let M:= (P i).weight; have hu : 0 ≤L i:= Nat.cast_nonneg _
      have hl : (1+ L i)^d' ≤ momentPrice (p.power*p.order) ξ * Real.exp (ξ*L i):= spendMoment _ ht hu
      have hm : F i*(Real.exp ((t+ξ)*L i) * Real.exp (b* coverNumber p.B (Q.halls i))) ≤ μW*(M*Real.exp (η*L i)):=by rw [show Q.halls i=(P i).postage.support from (congr_arg RegularAddress.support (h.quotes i).1.symm : _ )]; exact @Packet.glow G _ α p β (P i) ξ αP dθ (t+ξ) b η n k FX hP hβ he ht (h.high i).2 (h.high i).1 hb (by rw [(h.quotes i).1]; exact h.shape i) (by linarith only [hξ]) -- Q.halls mismatch RHS
      calc _ ≤ w^d'*(a*Real.exp (ξ*L i))*(F i* (Real.exp (t*L i) * Real.exp (b*coverNumber p.B (Q.halls i)))):=by have ht:=hz i; gcongr
           _ = (a*w^d')*(F i*(Real.exp ((t+ξ)*L i)*Real.exp (b*coverNumber p.B (Q.halls i)))):= by rw [add_mul,Real.exp_add]; ring
           _ ≤ _:=by rw [zero_mul,Real.exp_zero,mul_one,mul_assoc (a*w^d')]; exact mul_le_mul_of_nonneg_left hm (by positivity)
end Packet
end YM.RemainderComparison.Sagas
