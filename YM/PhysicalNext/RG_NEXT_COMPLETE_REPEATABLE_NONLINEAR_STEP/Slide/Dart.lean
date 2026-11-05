import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Slide.Keys
/-! # Core extraction in BULK by mirror polynomial of exact degree FOUR.
 Finite inert faces included before Rotation, no spurious Haar factor.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Slide
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck  Greenbelt
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c C L:Side} {Z D w m:ℕ}

abbrev Stars := Fin 5
def ray (j:Stars):ℝ:= (![1,-4,6,-4,(1:ℝ)] j) / ((2:ℝ)^4*24)
private lemma arms (a b: ℝ) (g h k l:ℝ→ℝ) (e f i j:Bool)
   (hb:g=(if e then (fun x=>a+x*b) else Function.const _ (g 0)))
   (he:h=(if f then (fun x=>a+x*b) else Function.const _ (h 0)))
   (hi:k=(if i then (fun x=>a+x*b) else Function.const _ (k 0)))
   (hk:l=(if j then (fun x=>a+x*b) else Function.const _ (l 0))):
   ∑ x:Stars,Slide.ray x*(g x.val*h x.val*k x.val*l x.val)=if e && f && i && j then b^4/2^4 else 0:= by
  conv_lhs => rw [hb,he,hi,hk]
  cases e <;> cases f <;> cases i <;> cases j <;> norm_num [Fin.sum_univ_succ,Stars,ray] <;> ring

lemma galaxie (v : Petals Z) (hp : 2*Z≤w):
    ∑ i:Stars, Slide.ray i * ∏ j,(Slide.dinners (w+i.val) (v j):ℝ) = if v=Slide.rosy Z then 1 else 0:= by
  let u:= ((w-2*Z+1:ℕ):ℝ); let g (i:Axis) (x:ℝ):= (match v i with |none => 2*u+x*2|some ⟨_,k⟩=> (coins k:ℝ))
  let e i:= decide (v i=none); have hx i:g i= if e i then (fun x :ℝ => 2*u+x*2) else Function.const ℝ (g i 0):= by funext j; simp only [g,e]; cases h:v i with|none=> simp|some val=> rcases val with ⟨b,k⟩; simp
  have hb i (j : ℕ) : (Slide.dinners (w+j) (v i):ℝ)=g i j:= by cases h:v i with
    | none=>
      simp only [g,h, dinners,u]; rw [show w+j-2*Z+1=(w-2*Z+1)+j by omega]; push_cast; ring
    | some v'=> obtain ⟨b,k⟩:=v'; dsimp only [g]; rw [h]; rfl
  have hu:e 0 && e 1 && e 2 && e 3 ↔ v=Slide.rosy Z:= by
    simp only [e,Bool.and_eq_true,decide_eq_true_eq]; constructor; · rintro ⟨⟨⟨hx,hv⟩,he⟩,h⟩; funext i; fin_cases i<;> assumption
    rintro rfl; exact ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩
  have h := arms (2*u) 2 (g 0) (g 1) (g 2) (g 3) (e 0) (e 1) (e 2) (e 3) (hx _) (hx _) (hx _) (hx _)
  simp_rw [hb, show (univ:Finset Axis)=({0,1,2,3}:Finset Axis) from (by decide)]; rw [if_congr hu rfl rfl] at h -- edit
  simp at * -- risk
  convert h using 2 with i; ring_nf
lemma collects (D : Stars→Side) (hp:0< Z) (hq:2*Z≤ w) (he : ∀ i,(D i).val=2*(w+i.val)) (f : Petals Z→ℝ) :
    ∑ i:Stars,Slide.ray i * ∑ x:Site (D i), f (charm (w+i.val) Z x)= f (Slide.rosy Z):= by
  let b (i:Stars):= charm (C:=D i) (w+i.val) Z
  have hb i : ∑ x:Site (D i), f (b i x)=∑ x:Petals Z,(∏ j,(Slide.dinners (w+i.val) (x j):ℝ))*f x:= by
    rw [← Finset.sum_fiberwise univ (b i)]; refine sum_congr rfl ?_; intro j _
    rw [sum_congr rfl (show ∀ x∈_, f (b i x)= f j from fun x (hx:x∈univ.filter fun x=>b i x=j)=> congr_arg f ((mem_filter.mp hx).2)), sum_const,nsmul_eq_mul]
    rw [show #(_)=∏ k,dinners (w+i.val) (j k) from weighted (he _) (hq.trans (Nat.le_add_right ..)) hp j,Nat.cast_prod]
  change ∑ i:Stars,ray i * (∑ x, f (b i x))=_; simp_rw [hb,mul_sum, ← mul_assoc]; rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul, Slide.galaxie _ hq]; simp
end YM.PhysicalNext.Repeat.Slide
