import YM.RG08.Carrel.Temple

/-! # Infinite cards enrollment and compatible cutoff approximation -/
noncomputable section
namespace YM.RG08.Carrel
open Camera Cloud Room Glyph Lattice Laurent Forms Pert.Bulk Isles Packets Filter Finset Function RG Extra.Iteration
open scoped Topology Classical BigOperators ENNReal
variable {I J:Type}{n k:ℕ}{G:Gauge}{P:Side}{τ σ p:ℝ}

-- generic accumulation of slides (ℓ¹ words as first stage)
def account (F:J→Flake n (Market I)):Flake n (Market I):=fun x=>∑' j,F j x

def paidC (F:J→Flake n (Market I))(σ p:ℝ):Prop:=0≤p∧∑' i,Cost (F i) σ ≤ ENNReal.ofReal p
namespace paidC
lemma one {F:J→Flake n (Market I)}(h:paidC F σ p)(i:J):Won (F i) σ p:=⟨h.1,(ENNReal.le_tsum i).trans h.2⟩
lemma tip {F:J→Flake n (Market I)}(h:paidC F σ p)(hh:0≤σ): Summable fun i:J×Slide I n=> F i.1 i.2 :=by
 have he : ∑' i:J×Slide I n,bill (F i.1 i.2) (σ*shelf i.2) ≠⊤:=by rw [ENNReal.tsum_prod'];exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h.2
 have ht:=bill_ne_top he
 exact (ht.of_nonneg_of_le (g:=fun i:J×Slide I n=>|F i.1 i.2|) (fun _=>abs_nonneg _) fun x=>le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg hh (show 0≤shelf x.2 from le_max_left ..)))).of_abs
lemma books {F:J→Flake n (Market I)}(h:paidC F σ p):Won (account F) σ p:=by
 refine ⟨h.1, le_trans (b:=∑' (x:Slide I n)(i:J),bill (F i x) (σ*shelf x)) (ENNReal.tsum_le_tsum fun x=>bill_tsum ..) ?_⟩;rw [ENNReal.tsum_comm];exact h.2

variable [Fintype I]
lemma uses {F:J→Flake n (Market I)}(h:paidC F σ p)(hh:0≤σ)(v:Vert P I)(i:Site P) : Summable (fun y:J×Slide I n=> F y.1 y.2 * per_use y.2 v i) :=by
 let K :ℝ:=∑ x:Tape n (Cove P I),|∏ j,v (x j)|
 have hv(y:Slide I n): |per_use y v i| ≤ K:=Finset.single_le_sum (f:=fun x:Tape n (Cove P I)=>|∏ j,v (x j)|) (fun x _=>abs_nonneg _) (mem_univ (aisle i y))
 have hc:=((h.tip hh).abs.mul_right K).of_nonneg_of_le (g:=fun y:J×Slide I n=>|F y.1 y.2 * per_use y.2 v i|) (fun _=>abs_nonneg _) (fun i=>by rw [abs_mul];exact mul_le_mul_of_nonneg_left (hv _) (abs_nonneg _))
 exact hc.of_abs
lemma counts {F:J→Flake n (Market I)}(h:paidC F σ p)(hh:0≤σ)(v : Vert P I): per_sum (account F) v=∑' j,per_sum (F j) v:=by
 let f (i:J)(y:Slide I n):=F i y*(∑ u:Site P,per_use y v u)
 have he : Summable (Function.uncurry f):=by
   have hs := summable_sum (s:=univ) (fun (i:Site P) _=>h.uses hh v i)
   simp only [←Finset.mul_sum] at hs; exact hs.congr (by rintro ⟨i,x⟩; rfl)
 unfold per_sum account; simp_rw [←tsum_mul_right]; exact he.tsum_comm
end paidC

def mass (a:J→Atom G n)(N:ℕ):Flake N (Market (Rayk G 1)):=account (fun i=>stored (a i) N)

lemma fleet (G:Gauge)(n N:ℕ){σ:ℝ}(h:0<σ):∃ C:ℝ,0≤C∧∀ {J:Type}{a:J→Atom G n}{p:ℝ}, Charged a σ p → paidC (fun i=>stored (a i) N) (σ/32) (p*C):=by
 obtain ⟨C,hC,hP⟩:=store_paid G h n N
 refine ⟨_,hC,fun {J a p} ⟨hB,hS,ht⟩ =>⟨mul_nonneg ((tsum_nonneg hB).trans ht) hC,?_⟩⟩
 apply (ENNReal.tsum_le_tsum fun j=> (hP (a j)).2).trans _
 rw [← ENNReal.ofReal_tsum_of_nonneg (f:=fun i=>(a i).budget σ * C) (fun i=>mul_nonneg (hB i) hC) (hS.mul_right C), tsum_mul_right]; gcongr

lemma stored_viewSum (a:Atom G n)(P:Side)(N:ℕ)(v:Vert P (Rayk G 1)): (∑ o:Site P,MvPolynomial.eval v (tap N (flask (showAtom a o))))=per_sum (stored a N) v:=by
 unfold per_sum;simp_rw [stored_view,Finset.mul_sum];rw [Summable.tsum_finsetSum]
 -- single paidC on Unit
 obtain ⟨K,hK,h⟩:= store_paid G (by norm_num : (0:ℝ)<1) n N; let F (_:Unit):=stored a N; let c:= a.budget 1*K
 have hp:paidC F (1/32) c:=⟨(h a).1,by simp [F];simpa [c] using (h a).2⟩
 intro i _;exact (hp.uses (by positivity) v i).comp_injective (i:=Prod.mk ()) (fun x y he=>Prod.mk.inj he|>.2)

/-- Nonlinear higher terms of all paths bought on same prelist. At n=0 field-independent
 price/report not asserted homogeneous (count cells separately); at k>0 equality to finite tori
ev with world's full given logs, ring tessellation not truncated. -/
theorem fare (G:Gauge)(n k:ℕ){σ:ℝ}(he:0<σ):∃ C:ℝ,0≤C∧∀ {J:Type} {a:J→Atom G n}{p:ℝ},Charged a σ p →
    (let F:= grown (mass a k); Held (carpet _) (σ/32) (p*C) F ∧
      ∀ (P:Side) (i:Fin k)(v:Vert P (Rayk G 1)),
          (∑ z:Tape k (Cove P (Rayk G 1)),pour F i z * (∏ j,v (z j))) = ∑' b, ∑ o:Site P, MvPolynomial.eval v (tap k (flask (showAtom (a b) o)))):=by
 obtain ⟨C,hC,H⟩:=fleet G n k he
 refine ⟨C,hC,fun {J a p} h=>⟨grown_held (paidC.books (H h)),fun P i v=>?_⟩⟩
 change (∑ z:Tape k (Cove P (Rayk G 1)),pour (grown (account _)) i z * (∏ j,v (z j)))=_
 rw [purchased _ (word_sum ((H h).books) (by positivity)),(H h).counts (by positivity)]; exact tsum_congr fun j=>(stored_viewSum (a j) P k v).symm

end YM.RG08.Carrel
