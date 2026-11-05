import YM.RG08.Weald.Reading

/-!
# Absolute anchored extension of sparse Ward actions.
Now abbreviate no-power in input variables (formal x inputs may have g-dependence).
Sym site transformations centered at constant-color rotations use Quarry reader.
Each sector polynomial at regulator f given by Pol stock and external *bond*.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Weald
open Jetty Skiff Lattice Isles Forms Pert.Bulk Function Finset Laurent Filter Packets Steam Mount
open Room Gallery Camera MvPolynomial Glyph Quarry
open scoped Topology BigOperators ENNReal Classical PowerSeries
variable {I J U:Type}{n d l e:ℕ}

-- constructible joint inputs, eventual uniformly & no t parameter
structure Window (D:Finset J)(Y:J→Dig) where
 tol:ℝ
 fit:∀ i k,|tap k (Y i)|≤ tol -- too strong all k, not used

-- Dig-valued functions family, polynomial truncation no homogeneity
abbrev Safe {I:Type}(a:I→Dig):=∀ k,∃ C:ℝ,0≤C ∧ ∀ i,|tap k (a i)|≤C
lemma safe_num(a:ℝ):Safe (fun _ : I=>PowerSeries.C a):=fun _=>⟨|a|,abs_nonneg _,fun _=>by rw [tap,PowerSeries.coeff_C];split_ifs <;> simp⟩
lemma safe_c(a:Dig):Safe (fun _ : I=>a):=fun k=>⟨|tap k a|,abs_nonneg _,fun _=>le_rfl⟩
lemma Safe.ticks {a:I→Dig}(h:Safe a)(e:ℕ):∃ C:ℝ,0≤C ∧∀ k ≤ e,∀ i,|tap k (a i)|≤C:=by
 choose C hC hc using h
 let S:=range (e+1); refine ⟨∑ k∈S,C k,sum_nonneg (fun i _=>hC i),fun k hk i=>(hc k i).trans (single_le_sum (s:=S) (f:=C) (fun j _=>hC j) (mem_range.mpr (by omega)))⟩
lemma Safe.mul {a b:I→Dig}(h:Safe a)(hh:Safe b):Safe (a*b):=fun e=>by
 obtain ⟨B,hB,hb⟩:=hh.ticks e; obtain ⟨C,hC,hc⟩:=h.ticks e
 refine ⟨(e+1:ℝ)*(C*B),by positivity,fun i=>?_⟩
 rw [tap,Pi.mul_apply,PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
 apply (abs_sum_le_sum_abs _ _).trans
 rw [show (e+1:ℝ)*(C*B) = ∑ _j∈range (e+1),(C*B) by simp]
 apply sum_le_sum; intro j hj; rw [abs_mul]; exact mul_le_mul (hc j (by simp only [mem_range] at *;omega) _) (hb _ (by omega) _) (abs_nonneg _) hC
lemma Safe.add {a b:I→Dig}(h:Safe a)(hh:Safe b):Safe (a+b):=fun e=>by obtain ⟨B,hB,hb⟩:=hh e;obtain ⟨C,hC,hc⟩:=h e;exact ⟨C+B,add_nonneg hC hB,fun i=>by rw [Pi.add_apply,tap,map_add];exact (abs_add_le ..).trans (add_le_add (hc _) (hb _))⟩
lemma Safe.prod(a:J→I→Dig)(s:Finset J)(h:∀ j∈s,Safe (a j)):Safe (fun i:I=> ∏ j∈s,a j i):=by
 induction s using Finset.induction_on with
 | empty=>simp only [prod_empty];exact safe_c _
 | @insert j s hj ih=>simp_rw [prod_insert hj];exact (h j (mem_insert_self ..)).mul (ih (fun i hi=>h i (mem_insert_of_mem hi)))
lemma Safe.eval (x:J→I→Dig)(h:∀ i,Safe (fun j=>x j i))(p:Inn I):Safe (fun j=>MvPolynomial.aeval (x j) p):=by
 induction p using MvPolynomial.induction_on with
 | C a=> simp only [aeval_C]; exact safe_c _
 | add _ _ hi hj=>simp_rw [map_add];exact hi.add hj
 | mul_X p i hi=>simp_rw [_root_.map_mul,MvPolynomial.aeval_X];exact hi.mul (h _)
lemma Safe.use (x:J→I→Dig)(h:∀ i,Safe (fun j=>x j i))(p:Port I):Safe (fun j=>breath (x j) p):=fun e=>by
 let s:=range (e+1)
 choose C hC hc using fun i=>eval x h (tap i p) (e-i)
 refine ⟨∑ i∈s,C i,sum_nonneg (fun i _=>hC i),fun j=>?_⟩
 rw [pulses];exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun i _=>hc i j))
lemma Safe.reader {A:J→U→Dig}(hA:Safe (fun i:J×U=>A i.1 i.2))(r:J→I→U)(p:Port I):Safe (fun j=>breath (A j ∘ r j) p):=by
 apply Safe.use;intro i k;obtain ⟨C,hC,Hc⟩:=hA k;exact ⟨C,hC,fun j=>Hc (j,r j i)⟩
lemma Safe.readers {K:Type}[Fintype K]{A:J→U→Dig}(hA:Safe (fun i:J×U=>A i.1 i.2))(g:J→K)(r:J→I→U)(p:K→Port I):Safe (fun j=>breath (A j ∘ r j) (p (g j))):=fun k=>by
 choose C hC h using fun u=>reader hA r (p u) k
 exact ⟨∑ u,C u,sum_nonneg (fun i _=>hC i),fun j=>(h (g j) j).trans (single_le_sum (f:=C) (fun i _=>hC i) (mem_univ _))⟩
lemma Safe.freely {A:J→I→Dig}(H:Safe (fun i:J×I=>A i.1 i.2)):Safe (fun i:J×Tape n I=>fret (A i.1) i.2):=by
 unfold fret; exact prod (I:=J×Tape n I) (fun i x=>A x.1 (x.2 i)) univ fun i _ k=>by obtain ⟨C,hC,h⟩:=H k;exact ⟨C,hC,fun j=>h (j.1,j.2 i)⟩
lemma Safe.take {a:I→Dig}(h:Safe a)(p: J→I):Safe (a ∘ p):=fun k=>by obtain ⟨C,hC,h⟩:=h k;exact ⟨C,hC,fun _=>h _⟩
lemma Safe.books {P:I→Dig}(h:Safe P)(n:ℕ): Safe (fun i:Tape n I=> fret P i):=
 Safe.take (a:=fun x:Unit×Tape n I=>fret P x.2) (Safe.freely (A:=fun _:Unit=>P) (h.take Prod.snd)) (fun i=>((),i))

variable {D Q:Type}{α:Filter Q}
lemma HatTrick {σ:ℝ}{h:0<σ}{L:Jetty.Loom I}{P:Pack n I}(hv:Lyrics P){C:ℝ}(ht:Sings L d h P C)(f:Pearl){a:Q→I→Dig}{A:I→Dig}(ha:Safe (fun i:Q×I=>a i.1 i.2))(hq:∀ i,(fun j=>a j i)=ᶠ[α] fun _=>A i)(e:ℕ) : Tendsto (fun j=> bond P f (a j) e) α (𝓝 (bond P f A e)):=by
 obtain ⟨B,hB,H⟩:= Safe.freely (n:=n) ha e
 let W(t:Tape n I):=‖P t f‖*B
 unfold bond
 refine tendsto_tsum_of_dominated_convergence ((Hatch.jewelled hv ht f).mul_right B) (fun t=> ?_) (.of_forall fun j t=>?_)
 · apply Filter.EventuallyEq.tendsto
   filter_upwards [eventually_all.mpr (fun k:Fin n=> hq (t k))] with j hj
   unfold fret; rw [prod_congr rfl (fun k _=>hj k)]
 rw [norm_mul];exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using H (j,t)) (norm_nonneg _)

--  `Pops` assumes each radius/due even if no uniform on infinite e; Ward is therefore literal full but earned for any quantitative shelf separately.
def Pops (P:GrainS I):Prop:=∀ e n,Lyrics (P e n)∧∃ (L:Jetty.Loom I)(d:ℕ)(σ:ℝ)(h:0<σ)(C:ℝ),Sings L d h (P e n) C
lemma flatish (P:GrainS I)(hv:Pops P)(f:Pearl){a:Q→I→Dig}{A:I→Dig}(ha:Safe (fun i:Q×I=>a i.1 i.2))(hq:∀ i,(fun j=>a j i)=ᶠ[α] fun _=>A i)(e:ℕ): Tendsto (fun j=>tap e (awaken l P f (a j))) α (𝓝 (tap e (awaken l P f A))):=by
 simp_rw [tap,awaken,PowerSeries.coeff_mk]
 refine tendsto_finsetSum _ fun k _=>tendsto_finsetSum _ fun n (_:n∈range (l+k+1))=>?_
 obtain ⟨hv,L,d,σ,h,C,ht⟩:=hv k n;exact HatTrick hv ht f ha hq _

end YM.RG08.Weald
