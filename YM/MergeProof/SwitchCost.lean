import YM.MergeProof.SwitchProd
import YM.ProofPorts.GRID_RENEWED_RESERVES.Rain


set_option autoImplicit false
noncomputable section
namespace YM.Merge.Switch
open Function Set Finset Filter Marker GridRenewal.Rain
open scoped Topology BigOperators Classical
variable {ι U A W : Type} [Fintype ι]

lemma Paid.congr {f g : U → Ways ι}{a:ℝ}(h:Paid f a) (he:∀ u x,x∈Set.Icc (0:ℝ) 1→f u x=g u x): Paid g a := by
  obtain ⟨b,hb,hA,H⟩:=h; refine ⟨b,hb,hA,fun u=>?_⟩; obtain ⟨g',hx,ht⟩:=H u; exact ⟨g',⟨fun x hr=> (hx.current x hr).trans (he u x hr),hx.converge⟩,ht⟩
omit [Fintype ι] in
lemma cong {f g:Ways ι}(h: ∀ᶠ x in 𝓝[>] (0:ℝ), f x=g x): jet f=jet g:=by
  ext i; have he : Filter.map (fun x=>decode f x i) (𝓝[>] (0:ℝ))=Filter.map (fun x=>decode g x i) _ := Filter.map_congr (h.mono fun x hp=> show decode f x i=decode g x i from by rw [decode,decode,hp]); unfold jet limUnder; rw [he]

lemma paidTerms (n : ℕ){f : U → Ways ι}{a : ℝ}(h : Paid f a) : Paid (fun u x v=>slide (f u x v) n) (slide a n):=by
  have he:‖(↑n.factorial:ℝ)⁻¹‖=(↑n.factorial:ℝ)⁻¹:=Real.norm_of_nonneg (by positivity)
  convert! ((h.pow n).smul ((↑n.factorial:ℝ)⁻¹)) using 1
  · ext i u y; simp [slide,smul_eq_mul,div_eq_mul_inv,mul_comm]
  rw [he]; unfold slide; ring
lemma Paid.exponential {f : U → Ways ι}{a : ℝ}(h:Paid f a) : Paid (fun u x p=> Real.exp (f u x p)) (Real.exp a):=by
  have he := issue (fun n=>paidTerms n h) ((meter a).summable)
  simp_rw [show ∀ i x v, (∑' n, slide (f i x v) n)=_ from fun _ _ _=>(meter _).tsum_eq] at he;convert! he.1; exact (meter a|>.tsum_eq.symm)



-- Map the jet produced by lifting into the intended marker ring.
-- A marker in ι is an independent switch; target V can have prohibited
-- combinations. Must send each switch to a truly square-zero element.
variable {V : Type} [DecidableEq V] (R : Census V)
def mapScores (r : ι→Poly R) : Score ι →ₗ[ℝ] Poly R := {
  toFun := fun p => ∑ i, ((p i:ℂ)) • ∏ j∈i,r j
  map_add' := fun x y=> by simp [add_smul,Finset.sum_add_distrib]
  map_smul' := fun x p=>by simp only [RingHom.id_apply,Finset.smul_sum, Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul,mul_smul];rfl }
variable {R}
lemma mapScores_apply (r : ι→Poly R)(p:Score ι):mapScores R r p=∑ i, (↑(p i):ℂ) • ∏ j∈i,r j:=rfl
lemma mapBench (r : ι→Poly R)(c : ℝ) (p : Finset ι): mapScores R r (bench p c)=(↑c:ℂ) • ∏ i∈p,r i:=by
  rw [mapScores_apply,sum_eq_single p]
  · simp [bench]
  · intro b _ hb; simp [bench,hb]
  simp

lemma cap_combs (r:ι→Poly R)(hr:∀ i,r i * r i=0)(p q:Score ι): mapScores R r (comb 0 p q)=mapScores R r p*mapScores R r q:=by
  have hp(x : Finset ι): (↑(comb 0 p q x):ℂ) • (∏ j∈x,r j) = ∑ j : Finset ι × Finset ι, (↑(if x=j.1∪j.2 then (0:ℝ)^(j.1∩j.2).card*p j.1*q j.2 else 0):ℂ) • (∏ j∈x,r j) := by rw [comb, Complex.ofReal_sum,Finset.sum_smul]
  simp_rw [mapScores_apply,hp]; rw [Finset.sum_comm, Fintype.sum_prod_type,Finset.sum_mul]; refine Finset.sum_congr rfl fun i _=> ?_
  rw [Finset.mul_sum];apply Finset.sum_congr rfl; intro j _
  rw [sum_eq_single (i ∪ j)]
  · simp only [↓reduceIte]
    by_cases h : Disjoint i j
    · rw [prod_union h, disjoint_iff_inter_eq_empty.mp h,Finset.card_empty,pow_zero,one_mul,Complex.ofReal_mul, smul_mul_smul_comm]
    have he : (i∩j).Nonempty:= nonempty_iff_ne_empty.mpr (disjoint_iff_inter_eq_empty.not.mp h)
    rw [zero_pow (Nat.ne_of_gt (card_pos.mpr he)),zero_mul,zero_mul,Complex.ofReal_zero,zero_smul, smul_mul_smul_comm]
    obtain ⟨x,hx⟩:=he; obtain ⟨hi,hj⟩:= Finset.mem_inter.mp hx
    rw [← mul_prod_erase _ _ hi, ← mul_prod_erase _ _ hj,mul_mul_mul_comm,hr,zero_mul,smul_zero]
  · intro b _ hb; rw [if_neg hb]; simp
  simp

def sound (r:ι→Poly R) (g:Ways ι): Poly R:=mapScores R r (jet g)
lemma Paid.works {f:U → Ways ι}{a:ℝ}(h:Paid f a)(u:U): ∃ g, Models (f u) g :=by obtain ⟨b,-,-,h⟩:=h; exact ⟨_,(h u).choose_spec.1⟩
lemma add_sounds (r:ι→Poly R){f g f' g':Ways ι}(h:Models f f')(he:Models g g'): sound r (f+g)=sound r f+sound r g:= by
  unfold sound; rw [(h.add he).exact,h.exact,he.exact]; exact map_add ..
lemma mul_sounds (r:ι→Poly R)(hr:∀ i,r i * r i=0){f g f' g':Ways ι}(h:Models f f')(he:Models g g'): sound r (f*g)=sound r f*sound r g:= by
  unfold sound; rw [(h.mul he).exact,h.exact,he.exact]; exact cap_combs r hr ..
lemma const_sounds (r:ι→Poly R)(c:ℝ): sound r (fun _ _=>c)=Poly.bead R (↑c):= by
  rw [sound,show (fun (_:ℝ) (_:Finset ι)=>c)=click ∅ c from (by ext; simp [click]),(modelClick _ _).exact, mapBench]; rw [Finset.prod_empty,← Poly.product_bead,mul_one]
lemma pow_sounds (r:ι→Poly R)(hr:∀ i,r i*r i=0){f:Ways ι}{a:ℝ}(h : Paid (fun _ : Unit=>f) a) (i:ℕ): sound r (f^i)=sound r f^i:=by
  induction i with
  | zero => rw [pow_zero,pow_zero]; exact (const_sounds r 1).trans (by simp only [Complex.ofReal_one,map_one])
  | succ i he => rw [pow_succ,pow_succ,mul_sounds r hr (show Models (f^i) _ from ((h.pow i).works ()).choose_spec) ((h.works ()).choose_spec),he]

local instance : IsTopologicalSemiring (Poly R) where
lemma soundTerms (r:ι→Poly R)(hr:∀ i,r i*r i=0){f:Ways ι}{a:ℝ}(h: Paid (fun _ : Unit=>f) a)(i:ℕ): sound r (fun x v=> slide (f x v) i)= GridRenewal.Rain.term (sound r f) i:=by
  let c:= (↑i.factorial:ℝ)⁻¹
  let v : Ways ι:=fun _ _=> c
  have hp:Paid (fun _:Unit=>v) ‖c‖:=constant (fun _=>c) (norm_nonneg _) (fun _=>le_rfl)
  rw [show (fun x p=> slide (f x p) i)= v*(f^i) by ext x p; simp [slide,v,c,div_eq_mul_inv,mul_comm]]
  rw [mul_sounds r hr (show Models v _ from (hp.works ()).choose_spec) (show Models (f^i) _ from ((h.pow i).works ()).choose_spec), const_sounds,pow_sounds r hr h,Poly.product_bead]; simp only [c,Complex.ofReal_inv,Complex.ofReal_natCast]; rfl

lemma soundSum (r:ι→Poly R) (f : A→Ways ι){F : Ways ι}{a : A→ℝ}
    (h:∀ i,Paid (fun _:Unit=> f i) (a i))(he:Summable a)(H:∀ x∈Set.Icc (0:ℝ) 1,∀ v, ∑' i, f i x v= F x v): HasSum (fun i=>sound r (f i)) (sound r F):= by
  let G := fun x v=> ∑' i, f i x v; have hg : jet F=jet G:=cong (approached.mono fun i hi=> funext fun j=> (H _ ⟨hi.1.le,hi.2⟩ j).symm)
  have hx:= fun v=> (issue h he).2 () v
  have hb : HasSum (fun i=>jet (f i)) (jet G):=by
    apply tendsto_pi_nhds.mpr; intro i; have hi:=hx i; unfold HasSum at *; simpa only [Finset.sum_apply] using hi
  unfold sound; rw [hg]; exact (mapScores R r).toContinuousLinearMap.hasSum hb
lemma soundExp (r:ι→Poly R)(hr:∀ i,r i*r i=0){f:Ways ι}{a:ℝ}(h: Paid (fun _ : Unit=>f) a) : sound r (fun x i=>Real.exp (f x i))=cyclone (sound r f):=by
  have he : HasSum (fun i=> GridRenewal.Rain.term (sound r f) i) (sound r (fun x i=>Real.exp (f x i))):= by
    simp_rw [← soundTerms r hr h]; exact soundSum r _ (fun n=>(paidTerms n h)) ((meter a).summable) (fun x _ i=> (meter _).tsum_eq)
  exact he.tsum_eq.symm
end YM.Merge.Switch
