import YM.TraceExtension.Loft.Prise
import YM.TraceExtension.Foundation.Dilate
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Kits
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det Loft
open Source Source.Drops Labels Work Planned.PrimaryIntegral295 Place Parts Next.Foundations WardBin
open scoped BigOperators Topology ContDiff ComplexConjugate Classical
variable {d n k:ℕ}{G:Gauge}{s:Side}
lemma tile_spec {M:Tensor.T (Snap G d) ℂ n} (k:ℕ)(J:Jet G):
    Labels.read J (tile M k)=∑ b:Fin n→ Fin (d-1), (if k=Parts.rate b then M (fun i=> (Pi.single (b i) (J (b i).val))) else 0):=by
   rw [← tile_reads]; let A:= trunk d J; let f(b:Fin n→ Fin (d-1)):= M fun i=>Pi.single (b i) (A (b i))
   have hx (t:ℝ): Tensor.diagonal M (engineered t A)=∑ b:Fin n→Fin (d-1), t^(Parts.rate b) • f b:=by
       unfold Tensor.diagonal; simp_rw [spread_scale]; rw[M.map_sum (fun i j=> t^((j:Fin (d-1)).val+2) • (Pi.single j (A j):Snap G d))]; apply sum_congr rfl fun b _=> ?_;rw[M.map_smul_univ, Finset.prod_pow_eq_pow_sum]; rfl
   change leading k (fun t=>Tensor.diagonal _ (engineered t A))=_; simp_rw[hx]; rw[lead_sum]; swap
   · intro i _; exact (monoSmooth ..).contDiffAt
   simp_rw [lead_monomial]; rfl
variable {F:Snap G d→ℂ}(H:ContDiffAt ℝ d F 0)(he:fderiv ℝ F 0=0)
private lemma tier_cut(k n:ℕ) (hp:k<n*2) : ∀ J:Jet G,Labels.read J (tile (Tensor.coeff F n 0) k)=0:=by
   intro J; rw [tile_spec]; apply sum_eq_zero fun i _=>?_ ; rw[if_neg]
   intro hh; apply hp.not_ge; rw[hh]; unfold Parts.rate; calc
     _ = ∑ i:Fin n, (2:ℕ):=by simp
     _ ≤ _ := sum_le_sum fun i _=> le_add_self
private lemma tier_zero (F:Snap G d→ ℂ)(k:ℕ)(J: Jet G): Labels.read J (tile (Tensor.coeff F 0 0) k)=(if k=0 then F 0 else 0):=by
   rw [tile_spec]; simp only [Parts.rate, sum_of_isEmpty,Tensor.coeff_apply_zero]; rw[sum_const,Finset.card_univ]; simp only [Fintype.card_fun,Fintype.card_fin, pow_zero, one_smul]
include he
private lemma tier_one (k:ℕ)(J:Jet G): Labels.read J (tile (Tensor.coeff F 1 0) k)=0:=by
   rw[tile_spec]; apply sum_eq_zero fun i _=>?_ ; split_ifs with hi; · simp [Tensor.coeff,iteratedFDeriv_one_apply,he]
   rfl
include H
lemma snap_low (J:Jet G)(hd:2≤d)(hk:k≤d)(hn:k≤5): leading k (fun t=> F (engineered t (trunk d J)))=(if k=0 then F 0 else 0)+ Labels.read J (tile (Tensor.coeff F 2 0) k):=by
   rw[Parts.leading_snap_sum H hk]; let K(i):=Labels.read J (tile (Tensor.coeff F i 0) k)
   change ∑ i∈range (d+1),K i=_; rw[← sum_subset (s₁:={0,1,2}) ?_ ?_]; rotate_left
   · intro i hi; simp only[mem_range]; simp only [Finset.mem_insert,mem_singleton] at hi; omega
   · intro i _ h; simp at h; exact tier_cut k i (by omega) _
   rw [Finset.sum_insert (?_:0 ∉ ({1,2}: Finset ℕ)), Finset.sum_insert (?_:1 ∉ ({2}:Finset ℕ)),sum_singleton]; rotate_left; try { decide }; try { decide }; unfold K; rw [tier_zero,tier_one he,zero_add]; all_goals decide
lemma snap_tiny (J:Jet G)(hd:2≤d)(hk:k≤d)(hn:k<4): leading k (fun t=> F (engineered t (trunk d J)))=if k=0 then F 0 else 0:=by rw[snap_low H he J hd hk (by omega),tier_cut k 2 (by omega) J,add_zero]
lemma snap_p4 (J: Jet G)(hd:4 ≤ d) :
    let a:Snap G d:=Pi.single (⟨0,by omega⟩:Fin (d-1)) (J 0)
    leading 4 (fun t=>F (engineered t (trunk d J)))= (1/2:ℝ) • iteratedFDeriv ℝ 2 F 0 ![a,a]:=by
   intro a; let i:Fin (d-1):=⟨0,by omega⟩; let p:Fin 2→ Fin (d-1):=![i,i]
   rw[snap_low H he J (by omega) hd (by omega),tile_spec, sum_eq_single p,if_neg (by decide),zero_add,if_pos (show 4=Parts.rate p from ?_)];
    -- from factor positivity
   · unfold Tensor.coeff; rw[_root_.smul_apply]; congr 2; · norm_num [Nat.factorial]
     ext1 k; fin_cases k<;> rfl
   · unfold rate; simp [p,i,Fin.sum_univ_two]
   · intro b hb h; refine if_neg (fun h'=> h (funext fun i=>?_)); unfold Parts.rate at h'; rw [Fin.sum_univ_two] at h'; apply Fin.ext; fin_cases i
     · change (b 0).val=0; omega
     change (b 1).val=0; omega
   intro h; exact (h (mem_univ _)).elim
lemma snap_p5 (J:Jet G)(hd:5 ≤ d):
    let a:Snap G d:=Pi.single (⟨0,by omega⟩:Fin (d-1)) (J 0); let b:Snap G d:=Pi.single (⟨1,by omega⟩: Fin (d-1)) (J 1)
    leading 5 (fun t=> F (engineered t (trunk d J)))=iteratedFDeriv ℝ 2 F 0 ![a,b]:=by
   intro a b; let i:Fin (d-1):=⟨0,by omega⟩; let j:Fin (d-1):=⟨1,by omega⟩; let p:Fin 2→ Fin (d-1):=![i,j]; let q:Fin 2→ _:=![j,i]; have hp:p ≠ q:=fun h=>by have ht:=congr_fun h 0; change i=j at ht; have hv:= congr_arg Fin.val ht; contradiction
   rw [snap_low H he J (by omega) hd le_rfl,tile_spec, if_neg (by decide),zero_add,← Finset.sum_subset (s₁:={p,q}) (subset_univ _) ?_]
   swap
   · intro t _ ht; apply if_neg; intro h; rw [Parts.rate,Fin.sum_univ_two] at h
     have he: ((t 0).val=0 ∧ (t 1).val=1) ∨ ((t 0).val=1∧ (t 1).val=0):=by omega
     cases he with
     | inl e=> apply ht; rw [show t=p from ?_]; · exact mem_insert_self ..
               funext k; fin_cases k; exact Fin.ext e.1;exact Fin.ext e.2
     | inr e=> apply ht; rw[show t=q from ?_]; · exact mem_insert_of_mem (mem_singleton_self ..)
               funext k; fin_cases k; exact Fin.ext e.1; exact Fin.ext e.2
   have hP: 5=Parts.rate p:=by unfold Parts.rate; rw [Fin.sum_univ_two]; rfl
   have hQ: 5=Parts.rate q:=by unfold Parts.rate; rw [Fin.sum_univ_two]; rfl
   let U:= Tensor.coeff F 2 0; rw[sum_insert (show p ∉ ({q}:Finset _) from by rwa [mem_singleton]),sum_singleton, if_pos hP, if_pos hQ,show (fun i:Fin 2=>Pi.single (p i) (J (p i).val))=![a,b] from ?_, show (fun i:Fin 2=>Pi.single (q i) (J (q i).val))=![b,a] from ?_]
   all_goals try (funext k; fin_cases k<;> rfl)
   have hh: U ![b,a]=U ![a,b]:=by
       have hx:Tensor.Sym U:= Tensor.coeff_symm (H.of_le (by exact_mod_cast (show 2≤d from by omega)))
       rw[show (![b,a]:Fin 2→_)=(![a,b]:Fin 2→_)∘ Equiv.swap 0 1 from ?_]; · exact hx _ _
       ext1 k; fin_cases k <;> simp
   rw[hh]; unfold U Tensor.coeff; rw [_root_.smul_apply]; calc
    _= (_:ℝ) • (iteratedFDeriv ℝ 2 F 0 ![a,b]) :=by rw[add_smul]
    _=_:=by norm_num [Nat.factorial]
end YM.Trace.Kits
