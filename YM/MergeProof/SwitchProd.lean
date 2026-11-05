import YM.MergeProof.Switch

set_option autoImplicit false
noncomputable section
namespace YM.Merge.Switch
open Function Set Finset Filter
open scoped Topology BigOperators Classical
variable {ι U A : Type} [Fintype ι]
-- Important: DecidableEq choice throughout. Avoid noncanonical typeclass loops.
def comb (x : ℝ)(p q : Score ι) : Score ι:= fun i=> ∑ j : Finset ι × Finset ι, if i=j.1∪j.2 then x^(j.1∩j.2).card*p j.1*q j.2 else 0

lemma colors (p q : Score ι) : high (comb 1 p q)=high p*high q:=by
  unfold high comb;rw [Finset.sum_comm]; simp only [one_pow,one_mul,Finset.sum_ite_eq',Finset.mem_univ, ↓reduceIte,Fintype.sum_prod_type, Finset.sum_mul,Finset.mul_sum] -- eq or eq'?
  exact Finset.sum_comm
lemma value_comb (x:ℝ)(p q : Score ι) : value x (comb x p q)=value x p*value x q:=by
  ext i; unfold value comb; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; simp_rw [mul_ite,mul_zero]
  let t (j:Finset ι) (k:Finset ι):=if j⊆i ∧ k⊆ i then x^j.card*p j*(x^k.card*q k) else 0
  change _=(value x p i)*(value x q i)
  rw [value_subset,value_subset]; have he j k: (if j⊆i then x^j.card*p j else 0)*(if k⊆i then x^k.card*q k else 0)=t j k:= by unfold t; by_cases h:j⊆i<;> by_cases h':k⊆i <;> simp [h,h']
  rw [Finset.sum_mul]; simp_rw [Finset.mul_sum,he]; rw [← Fintype.sum_prod_type (fun i:Finset ι × Finset ι=>t i.1 i.2)]
  apply Finset.sum_congr rfl; rintro ⟨u,v⟩ -; rw [sum_ite_eq']; dsimp only
  have hh : u∪v ∈ i.powerset ↔ u⊆i ∧ v⊆i := by simp [Finset.union_subset_iff]
  unfold t; simp_rw [hh]; split
  · rw [mul_mul_mul_comm _ _ (x^v.card),← pow_add,← Finset.card_union_add_card_inter u v,pow_add]; ring
  rfl

local notation "α" => 𝓝[>] (0:ℝ)
lemma Models.mul {f g f' g':Ways ι}(h:Models f f')(he:Models g g'): Models (f*g) (fun x=>comb x (f' x) (g' x)):= by
  refine ⟨fun x hx=> ?_,fun i=>?_⟩
  · rw [value_comb,h.current x hx,he.current x hx];rfl
  refine tendsto_finsetSum _ fun j _=> ?_
  split
  next => exact ((tendsto_id.mono_left (show α ≤ 𝓝 0 from nhdsWithin_le_nhds)).pow (j.1∩j.2).card|>.mul (h.converge j.1)|>.mul (he.converge j.2))
  next => exact tendsto_const_nhds

lemma comb_nn (p q:Score ι) (hp:∀ i,0≤p i)(hq:∀ i,0≤q i)(k):0≤comb 1 p q k:=sum_nonneg fun j _=>by split_ifs; exact mul_nonneg (mul_nonneg (by positivity) (hp _)) (hq _); rfl
lemma Bounded.mul {f g:Ways ι}{a b:Score ι}(h:Bounded f a)(hp:Bounded g b): Bounded (fun x=>comb x (f x) (g x)) (comb 1 a b):=by
  intro x hx i
  apply (norm_sum_le ..).trans; refine sum_le_sum fun j _=>?_; split
  next =>
    rw [norm_mul,norm_mul,norm_pow,Real.norm_of_nonneg hx.1]
    exact mul_le_mul (mul_le_mul (pow_le_pow_left₀ hx.1 hx.2 _) (h x hx _) (norm_nonneg _) (by positivity)) (hp x hx _) (norm_nonneg _) (mul_nonneg (by positivity) ((norm_nonneg _).trans (h x hx _)))
  next => rw [norm_zero]

variable {f g : U→Ways ι} {a b : ℝ}
lemma Paid.mul (h : Paid f a) (he:Paid g b):Paid (f*g) (a*b):=by
  obtain ⟨A,hA,h,H⟩:=h; obtain ⟨B,hB,h',H'⟩:=he
  refine ⟨comb 1 A B,comb_nn A B hA hB,?_,fun u=>?_⟩
  · rw [colors]; exact mul_le_mul h h' (sum_nonneg fun i _=> hB _) ((sum_nonneg fun i _=> hA i).trans h)
  obtain ⟨g,h,k⟩:= H u; obtain ⟨g',h',k'⟩:= H' u; exact ⟨_,h.mul h', k.mul k'⟩
lemma paidOne : Paid (1 : U→Ways ι) 1:= constant (fun _=>1) zero_le_one fun _=>norm_one.le -- adjust
lemma Paid.prod (u : Finset A)(g:A→U→Ways ι)(a:A→ℝ) (h:∀ i∈u,Paid (g i) (a i)): Paid (∏ i∈u,g i) (∏ i∈u,a i):=by
  induction u using Finset.induction with
  | empty => simp only [Finset.prod_empty];exact paidOne
  | insert i u hi ih => rw [prod_insert hi,prod_insert hi]; exact Paid.mul (h _ (mem_insert_self ..)) (ih fun i h' => h i (mem_insert_of_mem h'))
lemma Paid.pow (h : Paid f a)(n : ℕ) : Paid (f^n) (a^n):=by
  induction n with
  | zero => simp only [pow_zero]; exact paidOne
  | succ i hi=> rw [pow_succ,pow_succ]; exact hi.mul h
lemma Paid.smul (h:Paid f a)(b:ℝ): Paid (b • f) (‖b‖*a):=by
  have hp:= constant (ι:=ι) (fun _ : U=> b) (norm_nonneg b) (fun _=>le_rfl)
  exact Paid.mul hp h
lemma Paid.neg (h:Paid f a): Paid (-f) a:=by simpa using h.smul (-1)
lemma Paid.sub (h:Paid f a)(hp:Paid g b): Paid (f-g) (a+b):=by rw [sub_eq_add_neg]; exact h.add hp.neg
-- if comp doesn't depend on x or i. Sold if p value.
lemma Paid.gate {X : Set U}(h: Paid f a) : Paid (X.indicator f) a := by
  obtain ⟨b,h,hb,H⟩:=h; refine ⟨b,h,hb,fun u=>?_⟩; by_cases hz : u∈X
  · rw [indicator_of_mem hz]; exact H u
  rw [indicator_of_notMem hz]; refine ⟨0,⟨fun x _=>funext fun i=> ?_,fun v=>tendsto_const_nhds⟩,fun i _ v=>?_⟩
  · simp [value]
  change ‖(0:ℝ)‖≤ _;rw [norm_zero]; exact h _


-- Summable things. norm uniforms
lemma issue {f : A → U → Ways ι}{a:A→ℝ}(h: ∀ i,Paid (f i) (a i))(he:Summable a) :
    let F:=fun u x v=>∑' i,f i u x v; Paid F (∑' i,a i) ∧ ∀ u p,HasSum (fun i=> jet (f i u) p) (jet (F u) p) := by
  intro F
  choose b hb hB g hm hg using h
  have h (p : Finset ι): Summable (fun i=>b i p):=he.of_nonneg_of_le (fun i=>hb i p) (fun i=>(single_le_sum (fun u _=> hb i u) (Finset.mem_univ p)).trans (hB i))
  let G (u : U) (x:ℝ) (p:Finset ι):=∑' i,g i u x p
  have hh (u x p)(hx : x∈Set.Icc (0:ℝ) 1): Summable fun i=> ‖g i u x p‖:=(h p).of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=>hg i u x hx p)
  have hp (u:U) : Models (F u) (G u) := by
    constructor
    · intro x hx; funext p; simp_rw [F,←(hm _ _).current x hx]; unfold value G; simp_rw [← tsum_mul_left]; rw [Summable.tsum_finsetSum]; intro p _; exact ((hh u x p hx).of_norm).mul_left _
    intro i; exact tendsto_tsum_of_dominated_convergence (h i) (fun j => (hm j u).converge i) (approached.mono fun x hx a=>hg a u x ⟨hx.1.le,hx.2⟩ i)
  refine ⟨⟨fun p=>∑' i,b i p,fun p=> tsum_nonneg fun i=>hb i p,?_,fun u=> ⟨G u,hp u,fun x hx v=>(norm_tsum_le_tsum_norm (hh u x v hx)).trans ((hh u x v hx).tsum_le_tsum (fun i=>hg i u x hx _) (h _))⟩⟩,fun u p=>?_⟩
  · unfold high at *; rw [← Summable.tsum_finsetSum (f:=fun i a=> b a i) (hf:=fun i _=>h i)] -- signature?
    exact (summable_sum (fun i _=>h i)).tsum_le_tsum hB he
  rw [(hp u).exact]; simp_rw [(hm _ u).exact]; exact (hh u 0 p (show 0∈Set.Icc (0:ℝ) 1 from ⟨le_rfl,zero_le_one⟩)).of_norm.hasSum

end YM.Merge.Switch
