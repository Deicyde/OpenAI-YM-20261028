import YM.RG08.Wax.Girth
/-!
# Anchor counts at polymer join. Orientation-neutral. Include actual count of all
free marker roots, not allowing a varying set of paths depending on the tested
functionals. Fields in cover. Payment polypost only. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Wax
open Function Filter RG Lattice Laurent Stationary Quire Analysis Shade Vale Bands Loom Next.Free Bloch Scores Finset Push.AbsoluteSums UVExt.Paths Town Work.F08
open scoped Topology BigOperators Real Classical
variable {I E X:Type} [Fintype I] [DecidableEq I] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {i j k r s D:ℕ}{A B w v Z K θ R:ℝ}{W U V T:Finset I} {M:Row X X}

def shells (w:ℝ):= (2*((1+w)/w))^(Fintype.card Axis)
lemma shells_pos {w:ℝ}(h:0<w):0≤shells w:= by unfold shells; positivity
private lemma roll_off (x:Cover)(hp:0<w): SumBudget (fun y:Cover=>Real.exp (-w*size (y-x))) (shells w):= budget_pull (fun y:Cover=>y-x) (fun _ _ h=>sub_left_injective h) (Width.compactPay w hp)
lemma parcel_drop {P:Fleet T→ℝ} (t:↥T)(x:Cover)(hp: ∀ p,0≤P p)(hB:0≤B)(hv:0<v) (he:∀ x:Cover, SumBudget (fun i : Held t x=>P i.val) B) : SumBudget (fun y:Fleet T=> Real.exp (-v*size (y t-x))*P y) (B*shells v) := by
   let g y:= Real.exp (-v*size (y-x)); refine budget_fiberwise (p:=fun y:Fleet T=> y t) (fun i=> mul_nonneg (Real.exp_pos _).le (hp _)) ?_ (budget_scale hB (roll_off x hv)); intro i s ht
   let l(p:s):Held t i:= ⟨p.val,ht p.val p.property⟩; have hI : Injective l:= fun a b h=>Subtype.ext (congr_arg (fun y : Held t i=> y.val) h)
   change (∑ y ∈ s,g (y t)*P y) ≤ B*g i
   rw [← sum_coe_sort s, mul_comm B]; have hY (p:s): (p.val t)= i:= ht p.val p.property; simp_rw [hY, ← Finset.mul_sum]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; exact budget_sum (budget_pull l hI (he i)) univ

private lemma annular (T:Finset I)(p:Fleet T)(a:T): Mounts a p=∑ i∈T,size (loose T p i - p a):= by unfold Mounts; rw [← sum_coe_sort T]; exact sum_congr rfl fun i _=>by unfold loose; rw [dif_pos i.property]
def sent (i:W)(he:W ⊆ T): T:=⟨i.val, he i.property⟩ -- W
lemma mark_sum (ha:T=U∪V) (hd:Disjoint U V)(p:Fleet T)(t:T)(a:U)(b:V)(hx:sent a (show U⊆T from ha.symm ▸ subset_union_left)=t):
    let x:= pin U (loose T p); let y:=pin V (loose T p)
    Mounts t p ≤ Mounts a x + (Mounts b y+ V.card*size (p t-y b)) := by
  intro x y
  have hh:x a=p t:= hx ▸ (pin_loose T p|>.symm ▸ rfl)
  rw [annular, annular, annular]
  let w i:= size (loose T p i-p t); let v i:= size (loose V y i-y b)
  -- avoid dependent rewrite card T
  have hQ : ∑ i∈T,w i=(∑ i∈U,w i)+∑ i∈V,w i := (congr_arg (fun t:Finset I=>∑ i∈t, w i) ha).trans (sum_union hd)
  rw [show (∑ i∈T, _) = _ from hQ]
  refine Nat.add_le_add (le_of_eq ?_) ?_
  · apply sum_congr rfl; intro i hi; unfold w loose; rw [dif_pos hi, hh]; rfl
  change ∑ i∈V,w i ≤ (∑ i∈V,v i) + _
  rw [show V.card*size (p t-y b)=∑ _i∈V,size (p t-y b) from by simp,← sum_add_distrib]; refine sum_le_sum fun i hi=>?_ ; unfold w v; rw [show loose V y i=loose T p i from dif_pos hi,vibrate_sym (p t) (y b)]; exact vibrate ..
lemma par_knots (h:T=U∪V)(hd:Disjoint U V)(a:T)(b:U)(c:V)(hh:b.val=a.val)(hv:0<v)(hw:v≤w)(hk:V.card ≤ k)
    {f:Fleet U→ℝ}{g:Fleet V→ℝ}(hp:∀p,0≤f p)(hg:∀p,0≤g p)(hK:0≤K)(_hA:0≤A)(hB:0≤B)(hu:∀x, SumBudget (fun i : Held b x=> Tribe b i.val w (f i.val)) A)(hy :∀y, SumBudget (fun i : Held c y=> Tribe c i.val w (g i.val)) B) (x:Cover):
    SumBudget (fun i:Held a x=> let p:=i.val; let u:=pin U (loose T p); let y:=pin V (loose T p)
       Tribe a p v (Real.exp (-((k+1:ℕ)*v)*size (x-y c))*K*(f u*g y))) (K*(A*(B*shells v))) := by
    have ht : sent b (show U⊆T from h.symm ▸ subset_union_left)=a:=Subtype.ext hh
    let v' p:=pin V (loose T p)
    let u' p:=pin U (loose T p)
    have ha(p:Held a x): u' p.val b=x:= (show _=p.val a from ?_).trans p.property
    · let z (p:Held a x) := ((⟨u' p.val,ha p⟩:Held b x),v' p.val)
      have hl:= parcel_drop c x (P:=fun j=> Tribe c j w (g j)) (fun p=>mul_nonneg (Real.exp_pos _).le (hg _)) hB hv hy
      refine budget_mono (budget_scale hK (budget_pull z ?_ (budget_prod (hu x) hl))) (fun i=>mul_nonneg (Real.exp_pos _).le (mul_nonneg (mul_nonneg (Real.exp_pos _).le hK) (mul_nonneg (hp _) (hg _)))) ?_
      · intro p q hp; apply Subtype.ext; funext i
        have he (t:Held a x): t.val i=loose T t.val i.val:= congr_fun (pin_loose T t.val).symm i
        rw [he,he q]; have H : i.val∈U ∨ i.val∈V:= mem_union.mp (show i.val∈U∪V from h ▸ i.property)
        rcases H with h|h; · exact congr_fun (congr_arg (fun i:Held b x × Fleet V=>i.1.val) hp) ⟨i.val,h⟩
        exact congr_fun (congr_arg Prod.snd hp) (⟨i.val,h⟩: V)
      intro i; let x':=u' i.val; let y:=v' i.val
      have he : v*Mounts a i.val + -(((k+1:ℕ):ℝ)*v)*size (x-y c) ≤ w*Mounts b x'+ -v*size (y c - x)+w*Mounts c y:= by
          have ht': (Mounts a i.val:ℝ) ≤ Mounts b x'+((Mounts c y:ℝ)+ (k:ℝ)*size (x-y c)):= by
             have hz:=mark_sum h hd i.val a b c ht; dsimp only at hz
             rw [show i.val a=x from i.property] at hz; exact_mod_cast (hz.trans (add_le_add_right (add_le_add_right (Nat.mul_le_mul_right _ hk) _) _))
          rw [vibrate_sym (y c)]; push_cast; nlinarith only [mul_le_mul_of_nonneg_left ht' hv.le,mul_le_mul_of_nonneg_right hw (show 0≤(Mounts b x':ℝ) by positivity),mul_le_mul_of_nonneg_right hw (show 0≤(Mounts c y:ℝ) by positivity)]
      let n:= K*(f x'*g y); calc
           _ = Real.exp (v*Mounts a i.val+ -(((k+1:ℕ):ℝ)*v)*size (x-y c))* n:=by rw [Real.exp_add]; unfold Tribe n x' y u' v'; ring
           _ ≤ Real.exp (w*Mounts b x'+ -v*size (y c-x)+w*Mounts c y)* n:= mul_le_mul_of_nonneg_right (Real.exp_monotone he) (mul_nonneg hK (mul_nonneg (hp _) (hg _)))
           _ = _ := by simp only [Real.exp_add]; change _= K*(Tribe b x' w (f x')*(Real.exp _ * Tribe c y w (g y))); unfold Tribe n; ring
    change loose T p.val b.val=p.val a; rw [hh]; exact dif_pos a.property
end YM.RG08.Wax
