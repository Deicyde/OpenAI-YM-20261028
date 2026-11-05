import YM.FullVolume.E6.Spirits
import YM.FullVolume.E6.Sparse
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open FullVolume.Neptune
namespace Epoch
variable (R:Epoch Λ){l n k:ℕ}{r:ℝ}{u:ℕ→ Alphabet c f →ℝ}
set_option quotPrecheck false
local notation "X"=> footprints R.tubes R.kin Q.halo k
local notation "v"=> Sum.elim (Raw.forcedExtra R.kin) (Sum.elim (exCharge R.tubes R.kin) (fun _ : WarningAt c f=> 0))
local notation "t" => fun n=> tariff (u n) (fun i=> (v i:ℝ)) (fun _=>0) Q.ε
variable (h:∀ n, Sales (k) Q.relative Q.ε (footprints R.tubes R.kin Q.halo k) (u n) (Sum.elim (Raw.forcedExtra R.kin) (Sum.elim (exCharge R.tubes R.kin) (fun _ : WarningAt c f=> 0))) r)
abbrev opt (c f:Side)(j:LogIndex c f):Alphabet c f:= .inr (.inl j)
include h
lemma every (n): SumBudget (fun i=> t n (opt c f i)) (∑ _i:Site c,r):=by
    let F(p:Site c)(j: Alphabet c f):= if p ∈ X j then t n j * Real.exp (Q.relative*coverNumber k (X j)) else 0
    have hp p:SumBudget (fun i:LogIndex c f=>F p (opt c f i)) r:= budget_pull _ (show Injective (opt c f) from Sum.inr_injective.comp Sum.inl_injective) ((h n).hit p)
    have he:0≤Q.relative:=by unfold Target.relative; linarith [Q.usable,Q.bound,Q.pos]
    have hk i : 0≤ (t) n i:= mul_nonneg ((h n).nonneg i) (Real.exp_pos _).le
    refine budget_mono (budget_over Finset.univ _ _ (fun i _=>hp i)) (fun i=>hk _) ?_; intro i
    obtain ⟨b,hb⟩:= Coat.exChart S R.tubes R.kin k Q.halo i; apply le_trans _ (Finset.single_le_sum (f:=fun b=>F b (opt c f i)) (fun b _=> (hp b).1 _) (mem_univ b))
    unfold F; rw [if_pos (show b ∈ X (opt _ _ i) from hb)]; exact le_mul_of_one_le_right (hk _) (Real.one_le_exp (by positivity))
lemma sparseR (b:ℝ)(hb:0≤b)(j:ℕ): Sparse (fun n (i:LogIndex c f)=> if Loose i then u n (opt c f i)*(1+b * spanW R.tubes R.kin k Q.halo (.inr (opt c f i)))^j else 0):=by
   let C:=∑ _i:Site c,r; let d:=exCharge R.tubes R.kin
   obtain ⟨D,hD⟩:= (Set.finite_range (coverNumber (n:=c) k)).bddAbove
   let s:=1+(D:ℝ); let F:ℝ:=1+b*s+b; have hs:0≤ s:=by unfold s; positivity
   have hF:0≤F:= by unfold F; positivity
   let J i:ℝ:= 1+b*spanW R.tubes R.kin k Q.halo (Sum.inr (opt c f i))
   have hh i:J i≤F*(1+(d i:ℝ)):=by
          let Y:= X (opt _ _ i); change 1+b*(1+(coverNumber k Y+(d i:ℝ)))≤ _; have hs : (coverNumber k Y:ℝ)≤D:=by exact_mod_cast (show coverNumber k Y≤D from hD (mem_range_self Y))
          unfold F s
          have he :0≤(d i:ℝ):=by positivity
          nlinarith [show 0≤(D:ℝ) by positivity,show 0≤b*↑D*(d i:ℝ) by positivity, mul_le_mul_of_nonneg_left hs hb]
   have hv i:0≤J i:=by change 0≤1+b*(1+(coverNumber k (X (opt _ _ i))+(d i:ℝ))); positivity
   let a:=Q.ε; have ha:0<a:= Q.usable; let P:=a⁻¹^j * j.factorial* Real.exp a; have hP : 0≤P:= by unfold P; positivity
   let W:= fun n i=> if Loose i then u n (opt c f i)*(J i)^j else 0
   let V n i:= W n i*Real.exp (a*d i)
   have hJ n i:0≤W n i := by have hx:= (h n).nonneg (opt c f i); unfold W; split; exact mul_nonneg hx (pow_nonneg (hv _) _); rfl
   have hG (i:ℕ) : SumBudget (V i) ((F^j * P)*C):=by
        refine budget_mono (budget_scale (mul_nonneg (pow_nonneg hF _) hP) (every R h i)) (fun u=>mul_nonneg (hJ i _) (Real.exp_pos _).le) fun x=>?_
        by_cases hx:Loose x
        · let m:=opt c f x; have hg:J x^j ≤ F^j*(P*Real.exp (a*d x)) := calc
             _ ≤ (F*(1+(d x:ℝ)))^j:=by gcongr; exact hv x; exact hh x
             _ ≤ _ :=by rw [mul_pow]; apply mul_le_mul_of_nonneg_left (polynomial_cost ha (Nat.cast_nonneg _) _) (pow_nonneg hF _)
          unfold V W; rw [if_pos hx]; refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg ((h i).nonneg m)) (Real.exp_pos _).le).trans_eq ?_
          change _=F^j*P*(u i m*Real.exp (2*a*d x+0)); rw [show 2*a*(d x:ℝ)+0=a*d x+a*d x by ring,Real.exp_add]; ring
        unfold V W; rw [if_neg hx,zero_mul]; exact mul_nonneg (mul_nonneg (pow_nonneg hF _) hP) ((every R h i).1 _)
   let c:=F^j*P*C
   refine ⟨⟨_,fun n=> budget_mono (hG n) (show ∀ i,0≤ W n i from hJ n) (fun i=> le_mul_of_one_le_right (hJ n _) (Real.one_le_exp (mul_nonneg ha.le (Nat.cast_nonneg _))))⟩,fun v' he=>?_⟩
   obtain ⟨g,hg⟩:= (((Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop ha)).eventually_ge_atTop (c/v'))).exists
   obtain ⟨I,hI⟩:= R.hamlets g
   refine ⟨I,fun n T ht=>?_⟩; change ∑ i∈T,W n i≤ v'
   have hw k (hk:k∈T):W n k*Real.exp (a*g) ≤ V n k :=by
        by_cases hx:Loose k
        · apply mul_le_mul_of_nonneg_left (Real.exp_monotone _) (hJ n k)
          have H:g ≤ d k:=le_of_not_gt (fun h=> disjoint_left.mp ht (hI k hx h.le) hk); gcongr
        unfold V W; rw [if_neg hx,zero_mul,zero_mul]
   exact le_of_mul_le_mul_right ((by rw [sum_mul]; exact (sum_le_sum hw).trans (budget_sum (hG n) T) : (∑ i∈T, W n i)*Real.exp (a*g)≤ c).trans (((div_le_iff₀ he).mp hg).trans_eq (mul_comm ..))) (Real.exp_pos _)
end Epoch
end YM.ConnectedActivityE6.Lim
