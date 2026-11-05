import YM.MergeProof.Garden

set_option autoImplicit false
noncomputable section
namespace YM.Merge.Palette
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι] {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(Y:Cash W x μ L Q o C T R) (χ:Chi)
local notation "sx"=> radiusB x
open Blaze.March Multiple Ursell Trees Mixed Daisy OmitClusters Gas
variable (rA:ι→ℝ)
local notation "dc"=> ConnectedActivityE6.lengths T R
local notation "kd"=> steamP S (Q.costs L μ R.beta x C)
variable {P':Type}[Fintype P'] {d:ℝ}{N:ℕ}
omit [Fintype ι] in
private lemma birthCost (hp:foam Q L)(hM:R.p.B ≤ 2*(radiusB x))(M: Lotus.Leaf R)
    (he:4 ≤ Q.relative) : let U:= Y.birth (sparkling c f M.turn) -- edit
    (Q.relative+1)*(coverNumber (radiusB x) U:ℝ) ≤ (Q.relative+1)*Footprint.preCost (Q.halo+5)+(5/4:ℝ)*Q.ε*(coverNumber R.p.B M.crest):=by
   intro U
   have hx:0<radiusB x:= by have h:= Y.laws.data.room.sight.1; omega
   let v:= coverNumber R.p.B M.crest
   have h':= le_trans (Nat.cast_le (α:=ℝ).mpr (Lattice.Corona.cover_mono (sparkHead M Y|>.symm ▸ Footprint.inspected_price S.ratio Q.halo (radiusB x) M.crest hx) (radiusB x))) (footprint S.ratio _ _ R.p.B _ hx hM)
   apply (mul_le_mul_of_nonneg_left h' (show 0≤ Q.relative+1 from by linarith)).trans
   rw [mul_add, ← mul_assoc (Q.relative+1)]; refine add_le_add_right (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg (α:=ℝ) v)) _
   let w:= Footprint.conversion S.ratio (Q.halo+5); have hc:0≤ w:= by unfold w Footprint.conversion Footprint.preCost; positivity
   have hu: Q.relative*w ≤ Q.ε:=by unfold w Footprint.conversion; rw [show S.ratio.count=L from Y.laws.data.funds.length_eq]; exact hp
   change (Q.relative+1)*w≤ _; nlinarith

def shipPrice (L:Side) (Q:ConnectedActivityE6.Target G P) (x:ℝ)(N:ℕ)(a:ℝ): Prop:=
   N * Extra.Multi.siteFactor (radiusB x) * (Real.exp ((Q.relative+1)*Footprint.preCost (Q.halo+5)) * a) ≤ Daisy.ribbon Q L x
lemma deck (hp: ∀ i,0≤ rA i) (X':P'→Site f)(A:ι→Finset P')(hh : Extra.Multi.Occupancy (fun i=>S.ratio.parent (X' i)) N)(hz: ∀ i, 0<wages M rA i→∃ j∈A i,X' j∈ (M i).crest)(he: 4 ≤ Q.relative) (hy:100 ≤ R.p.supportExponent)(ht:foam Q L)(hv: R.p.B≤2*radiusB x)(hc:0≤ d)(hQ:Extra.Multi.Rooted A (fun i=>(M i).crest) R.p.B (R.p.supportExponent-4) (wages M rA) d)(hh':shipPrice L Q x N d): Plot M Y rA:=by
  let H:= Y.birth; let X(i:ι):= mark (c:=c) M i; let b i:= (M i).crest
  let mf i:= wages M rA i * Real.exp (2*Q.ε*dc (X i)+0)
  have hv' i:0 ≤ wages M rA i:= mul_nonneg (hp i) ((M i).profit); have hf i:0≤ mf i:= mul_nonneg (hv' i) (Real.exp_pos _).le
  let W:=Real.exp ((Q.relative+1)*Footprint.preCost (Q.halo+5)); have hW:0≤ W:=(Real.exp_pos _).le
  have hV:Extra.Multi.Rooted A (H ∘ X) sx (Q.relative+1) mf (W*d):=by
     intro i; refine Extra.Multi.Budget.mono (Extra.Multi.Budget.scale (hQ i) hW) (fun i=>?_) (fun j=> ?_) le_rfl
     · split; exact mul_nonneg (Real.exp_pos _).le (hf _); rfl -- intro?
     split_ifs; swap; · rw [mul_zero]
     unfold mf; rw [add_zero]
     have hz:=birthCost Y ht hv (M j) he -- order
     have hu:4*Q.ε < R.p.supportExponent:= Y.laws.intake.exponent ▸ Q.grants.1
     change 4*Q.ε < R.p.supportExponent at hu
     let v:=coverNumber R.p.B (b j); rw [show dc (X j)=(v:ℝ) from sparkExp (T:=T) (M j)]; unfold W
     rw [← mul_assoc (Real.exp ((Q.relative+1) * preCost _))]; rw [mul_comm (wages M rA j),← mul_assoc,← Real.exp_add,← Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (hv' _); apply Real.exp_monotone
     have he : 13/4* Q.ε ≤ R.p.supportExponent-4:=by linarith
     change (Q.relative+1)*(coverNumber sx ((H ∘ X) j):ℝ) ≤ (Q.relative+1)*Footprint.preCost (Q.halo+5)+(5/4:ℝ)*Q.ε*v at hz
     change _ ≤ _+(R.p.supportExponent-4)*v
     nlinarith only [hz,mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (α:=ℝ) v)]
  have ha:= Y.armed
  let X₀(i:ConnectedActivityE6.Alphabet c f):=Tickets.extra (X) (wages M rA) i
  have h:(Ac.Hit (H ∘ X) sx mf Q.relative (ribbon Q L x)):=by
    refine fun i=> Extra.Multi.Budget.mono (Extra.Multi.root_hit hh hf (mul_nonneg hW hc) ?_ hV i) ?_ (fun _=> le_rfl) hh'
    · intro i hu; obtain ⟨j,h,hk⟩:=hz i (pos_of_mul_pos_left hu (Real.exp_pos _).le); refine ⟨j,h,?_⟩; change _ ∈ Y.birth _; rw [show X i = sparkling c f (M i).turn from rfl,sparkHead]; exact halo_subset _ _ (mem_image_of_mem _ (mem_union_left _ hk))
    intro i; split; exact mul_nonneg (hf _) (Real.exp_pos _).le; rfl
  have hl: Ac.Hit H sx (Reserves.tariff X₀ dc (fun _=>0) Q.ε) Q.relative (ribbon Q L x):=by
    intro p; -- finite aggregate valuation
    refine budget_of_sum ?_ (fun V=> ?_)
    · intro i; split
      next =>
        have he j:0 ≤ (X₀ j):=sum_nonneg (fun i _=> by split; exact hv' _; exact le_rfl)
        exact mul_nonneg (mul_nonneg (he _) (Real.exp_pos _).le) (Real.exp_pos _).le
      next=> exact le_rfl
    let s i:= if p∈ (H ∘ X) i then mf i*Real.exp (Q.relative*coverNumber sx (H (X i))) else 0
    have he(i:ConnectedActivityE6.Alphabet c f):
        (if p∈H i then Reserves.tariff X₀ dc (fun _=>0) Q.ε i*Real.exp (Q.relative*coverNumber sx (H i)) else 0)=∑ j, if X j=i then s j else 0 :=by
       unfold X₀ Reserves.tariff Tickets.extra s mf
       by_cases hh:p∈ H i
       · rw [if_pos hh, sum_mul, sum_mul]; apply sum_congr rfl; intro j _; by_cases hv: X j=i <;> simp only [hv,hh,↓reduceIte,Function.comp_apply] ; first|rfl|simp
       rw [if_neg hh]; symm; refine sum_eq_zero (fun j _=>?_); split; next h'=> simp [Function.comp_apply,h',hh]
       next=>rfl
    simp_rw [he];rw [sum_comm]; refine le_trans (sum_le_sum (s:=(univ: Finset ι)) (g:=s) ?_) (budget_sum (h p) _)
    intro i _; simp [sum_ite_eq]; split; rfl;exact (h p).1 i
  refine ⟨⟨ha.packetBound,fun i=>add_nonneg (ha.holds i) ?_,ha.extra,fun i=>?_⟩,hp⟩
  · exact sum_nonneg fun i _=> by split; exact hv' _; exact le_rfl
  convert! budget_plus (ha.pays i) (hl i) using 1; ext j; dsimp only [H,pitch,Reserves.tariff,X₀,Cash.birth]; split <;> simp only [add_mul,add_zero] ; rfl
end YM.Merge.Palette
