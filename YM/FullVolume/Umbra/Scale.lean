import YM.FullVolume.Poesy.Soles
-- one real mark among any two epoch carpets at the same stamp
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
open FullVolume.Neptune Flux Shield Eider Packets Polar
namespace Umbra
-- power/copies calculus. first jet sparse gauge.
variable {α:Type} {b t:ℝ}
def priceJ (f:ℝ→ℝ) (t:ℝ):= DifferentiableAt ℝ f 0∧ |f 0| + |deriv f 0| ≤ t
lemma price_one : priceJ (fun _=>1) 1:=⟨differentiableAt_const _,by simp⟩
lemma price_zero : priceJ (fun _=>0) 0:=⟨differentiableAt_const _,by simp⟩
variable {f g:ℝ→ℝ}
lemma price_pos (h:priceJ f t):0≤t:= (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans h.2
lemma climbing (h:priceJ f b) (hp:b ≤ t):priceJ f t:= ⟨h.1,h.2.trans hp⟩
lemma combine (h:priceJ f b)(he:priceJ g t):priceJ (fun x=> f x*g x) (b*t):=by
   refine ⟨h.1.mul he.1,?_⟩; rw [deriv_fun_mul h.1 he.1,abs_mul]; apply le_trans (add_le_add_right (abs_add_le ..) _); rw [abs_mul,abs_mul]
   refine le_trans ?_ (mul_le_mul h.2 he.2 (add_nonneg (abs_nonneg _) (abs_nonneg _)) (price_pos h)); nlinarith [mul_nonneg (abs_nonneg (deriv f 0)) (abs_nonneg (deriv g 0))]
lemma scaleJ (h:priceJ f b)(z:ℝ):priceJ (fun i=> z*f i) (|z| *b):=by
     refine combine ?_ h; exact ⟨differentiableAt_const _,by simp⟩
lemma carryJ {g:α→ℝ→ℝ}{f:α→ℝ}(s:Finset α)(he:∀ i,priceJ (g i) (f i)):priceJ (fun u=> ∏ i∈s,g i u) (∏ i∈s, f i):=by
     induction s using Finset.induction_on with
     | empty=> simp only [Finset.prod_empty];exact price_one
     | insert i x h ih=>simp_rw [prod_insert h];exact combine (he i) ih
lemma ascend (h:priceJ f b)(k:ℕ):priceJ (fun x=> f x^k) (b^k):=by induction k with
                                                                        | zero=> simp only [pow_zero]; exact price_one
                                                                        | succ k ih=> simpa only [pow_succ] using! combine ih h
structure Steps (φ: Filter ℕ)(f g:ℕ→ℝ→ℝ):Prop where
    ready n : DifferentiableAt ℝ (f n) 0 ∧ DifferentiableAt ℝ (g n) 0
    value: Glints φ (fun n=> f n 0) (fun n=>g n 0)
    roofs: Glints φ (fun n=> deriv (f n) 0) (fun n=> deriv (g n) 0)
namespace Steps
variable {α ι:Type}{f g F H: ℕ→ℝ→ℝ}
lemma constant {f g:ℕ→ℝ}(ht:Glints φ f g):Steps φ (fun n _=>f n) (fun n _=>g n):=by
     exact ⟨fun _=>⟨differentiableAt_const _,differentiableAt_const _⟩,ht,by simp only [deriv_const]; exact ⟨_,tendsto_const_nhds,tendsto_const_nhds⟩⟩
lemma multiplies (h:Steps φ f g)(hv:Steps φ F H): Steps φ (fun n t=>f n t * F n t) (fun n t=>g n t *H n t):=by
     refine ⟨fun n=>⟨(h.ready n).1.mul (hv.ready n).1,(h.ready n).2.mul (hv.ready n).2⟩, h.value.prods hv.value continuous_mul,?_⟩
     simp_rw [fun i=> deriv_fun_mul (h.ready i).1 (hv.ready i).1,fun i=> deriv_fun_mul (h.ready i).2 (hv.ready i).2]; exact (h.roofs.prods hv.value continuous_mul).prods (h.value.prods hv.roofs continuous_mul) continuous_add
lemma constJ (a:ℝ): Steps φ (fun _ _=>a) (fun _ _=>a):=constant ⟨_,tendsto_const_nhds,tendsto_const_nhds⟩
lemma product {f g:α→ℕ→ℝ→ℝ}(s:Finset α) (h:∀ i, Steps φ (f i) (g i)):Steps φ (fun n u=>∏ i∈s, f i n u) (fun n u=>∏ i∈s,g i n u):=by
    induction s using Finset.induction_on with
    | empty=> simp only [Finset.prod_empty]; exact constJ _
    | insert i x he ih=>simp_rw [prod_insert he];exact (h i).multiplies ih
lemma power (h:Steps φ f g)(k:ℕ): Steps φ (fun n t=> f n t^k) (fun n t=>g n t^k):=by induction k with
                                                                                        | zero=> simp only [pow_zero];exact constJ _
                                                                                        | succ k ih=> simp_rw [pow_succ];exact ih.multiplies h
lemma switchJ (h:Steps (J:Filter ℕ) f g) (Q:ℕ→Prop) :Steps (J:Filter ℕ) (fun n x=>if Q n then f n x else 0) (fun n x=>if Q n then g n x else 0):=by
    let u n x:= if Q n then f n x else 0
    refine ⟨fun n=>?_, (switch h.value ⟨0,tendsto_const_nhds,tendsto_const_nhds⟩ Q),?_⟩
    · by_cases hh:Q n; simpa only [hh,if_true] using h.ready n
      simp only [hh,if_false]; exact ⟨differentiableAt_const _,differentiableAt_const _⟩
    apply (switch h.roofs ⟨0,tendsto_const_nhds,tendsto_const_nhds⟩ Q).carve; all_goals (filter_upwards with n; by_cases hh:Q n <;>simp [hh])
end Steps
section rough
variable {ι θ:Type}
abbrev Tilt (ι:Type)(G:Gauge)(n:Side):= ℕ→ ℝ→ι→ Config G n→ℝ
-- forward/backward
structure Back (F:Tilt ι G c): Prop where
    bins : ∃ v:ℕ→ι→ℝ, Sparse v ∧ ∀ n i V, priceJ (fun x=> F n x i V) (v n i)
structure Jade (F H:Tilt ι G c):Prop where
   a : Back F
   b : Back H
   converge i (V:ℕ→ Config G c) (J:Ultrafilter ℕ) (h:(J:Filter ℕ)≤ atTop): Steps (J:Filter ℕ) (fun n x=> F n x i (V n)) (fun n x=> H n x i (V n))
-- conversions.M
end rough
end Umbra
end YM.ConnectedActivityE6.Lim
