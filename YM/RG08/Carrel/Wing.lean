import YM.RG08.Carrel.Lease
import YM.Work.F03.Flat

/-! # Linear-curl leading reading, all ranks -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Carrel
open Camera Cloud Room Glyph Lattice Laurent Forms Pert.Bulk Isles Packets Filter Finset Function RG Extra.Iteration
open Wilson Exterior Precision Work.F03 MvPolynomial
open scoped Topology ContDiff Classical BigOperators ENNReal
variable {G:Gauge}{P:Side}{n:ℕ}

-- Real eval through scalar coordinates, not symmetrized tensor assumption.
def directors (G:Gauge) (a:Cellar (Bedge G P)):Bid.Dir G P:=fun x=>heavy G fun u=> a (x.1,x.2,u)
lemma offered_rep (a : Cellar (Bedge G P)):offers G a=represent (directors G a):=by
 funext e;rw [represent_link];rfl

abbrev curling (G:Gauge)(a:Vert P (Rayk G 1)) : Vert P (Rayk G 2):=fun i=> ((Exterior.dColor G P 1 (directors G a)) (i.1,i.2.1)) i.2.2
lemma filmed (G:Gauge)(N:ℕ)(u:Site P)(s:Slot)(i:G.ColorIndex):Camera.Pace (Kiss G u s i):=by
 obtain ⟨C,hc,h⟩:= kissing G N (by positivity : 0 < (1:ℝ));exact (h _ _ s i).analytic
lemma kiss_read (p:Site P)(s:Slot)(i:G.ColorIndex)(v:Vert P (Rayk G 1)):
 eval v (tap 1 (flask (Kiss G p s i))) = curling G v ((wrap P s.offset)+p,plaqEquiv s.plaq,i):=by
 let X:=Kiss G p s i
 have hc := glimpses (f:=X) (filmed G 1 ..) 1 v
 rw [iteratedFDeriv_one_apply] at hc;simp only [Nat.factorial_one,Nat.cast_one,inv_one, one_mul] at hc
 apply hc.trans
 let L : G.Color →L[ℝ] ℝ:= (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:G.ColorIndex=>ℝ) i).comp ((heavy G).symm.toContinuousLinearMap)
 let a:= directors G v
 have ht : HasDerivAt (fun t:ℝ=> X (t • v)) (L (faceCurl (slotFace s p) a)) 0 :=by
   convert! L.hasFDerivAt.comp_hasDerivAt (0:ℝ) (slot_deriv s p a) using 1
   funext t
   change s.atSite _ p i=s.atSite _ p i
   rw [offered_rep]
   have he:directors G (t • v)=t • directors G v:=by funext j;change heavy G (t • fun b=>v (j.1,j.2,b))=t • _;rw [(heavy G).map_smul];rfl
   rw [he]
 have he : HasDerivAt (fun t:ℝ=> X (t • v)) (fderiv ℝ X 0 v) 0:=by
    have hf:= ((filmed G 1 p s i).differentiableAt (by simp)).hasFDerivAt
    exact HasFDerivAt.comp_hasDerivAt (l:=X) (l':=fderiv ℝ X (0:_)) (0:ℝ) (by rw [zero_smul]; exact hf) (show HasDerivAt (fun r:ℝ=>r • v) v 0 from by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const v)
 exact he.unique ht

lemma at_first (a:Atom G n)(p:Site P)(v:Vert P (Rayk G 1)):
    eval v (tap n (flask (showAtom a p)))=a.poly (fun i=>faceCurl (slotFace (a.leg i) p) (directors G v)):=by
 let D (b:Fin n→G.ColorIndex) (i:Fin n) := Kiss G p (a.leg i) (b i)
 let Q(b:Fin n→G.ColorIndex):=∏ i:Fin n,D b i
 have hp b i:Pace (D b i):=filmed G n ..
 have ht b:Pace (Q b):=by simpa only [Q,←Finset.prod_apply] using (contDiffAt_prod (t:=univ) (f:=D b) (fun _ _=>hp _ _))
 have he: showAtom a p=∑ b:Fin n→G.ColorIndex, a.coeff b • Q b:=by funext i;simp only [Atom.unmasked,showAtom,Atom.poly,Finset.sum_apply, Q,Pi.smul_apply, smul_eq_mul,Finset.prod_apply,D];rfl
 have hex (i b) : flask (D b i)=PowerSeries.X*tax 1 (flask (D b i)):=Eq.symm (by
    rw [←pow_one (PowerSeries.X : Port (Bedge G P)),pay]; intro j hj;simp [tap,D,flask,print,show j=0 by omega])
 have hr b : ∏ i:Fin n,flask (D b i)=PowerSeries.X ^ n * ∏ i:Fin n,tax 1 (flask (D b i)):=by
    conv_lhs=>arg 2; intro j; rw [hex j b]
    simp [Finset.prod_mul_distrib]
 rw [he,slurry _ _ (fun b _=>show Pace (a.coeff b • Q b) from (ht b).const_smul (a.coeff b))]
 unfold tap Atom.poly;rw [map_sum,eval_sum];apply Finset.sum_congr rfl;intro b _;rw [flask_scale (ht b)];unfold Q;rw [slurry_prod _ _ (fun i _=>hp b i), PowerSeries.coeff_smul,hr,← MvPolynomial.aeval_eq_eval] -- inspect
 rw [PowerSeries.coeff_X_pow_mul',if_pos le_rfl,Nat.sub_self,PowerSeries.coeff_zero_eq_constantCoeff,map_prod,_root_.map_smul,MvPolynomial.aeval_prod,smul_eq_mul];congr 1; apply Finset.prod_congr rfl;intro j _
 rw [←PowerSeries.coeff_zero_eq_constantCoeff];change MvPolynomial.eval (v: Vert P (Rayk G 1)) (tap 0 (tax 1 _))=_;rw [audited];exact kiss_read ..


lemma before_first (a:Atom G n)(p:Site P)(k:ℕ)(h:k<n): tap k (flask (showAtom a p))=0:=by
 let D (b:Fin n→G.ColorIndex) (i:Fin n) := Kiss G p (a.leg i) (b i)
 let Q(b:Fin n→G.ColorIndex):=∏ i:Fin n,D b i
 have hp b i:Pace (D b i):=filmed G n ..
 have ht b:Pace (Q b):=by simpa only [Q,←Finset.prod_apply] using (contDiffAt_prod (t:=univ) (f:=D b) (fun _ _=>hp _ _))
 have he: showAtom a p=∑ b:Fin n→G.ColorIndex, a.coeff b • Q b:=by funext i;simp only [Atom.unmasked,showAtom,Atom.poly,Finset.sum_apply,Q,Pi.smul_apply,smul_eq_mul,Finset.prod_apply,D];rfl
 have hex (i b) : flask (D b i)=PowerSeries.X*tax 1 (flask (D b i)):=Eq.symm (by
    rw [←pow_one (PowerSeries.X : Port (Bedge G P)),pay]; intro j hj;simp [tap,D,flask,print,show j=0 by omega])
 have hr b : ∏ i:Fin n,flask (D b i)=PowerSeries.X ^ n * ∏ i:Fin n,tax 1 (flask (D b i)):=by
    conv_lhs=>arg 2; intro j; rw [hex j b]
    simp [Finset.prod_mul_distrib]
 rw [he,slurry _ _ (fun b _=>show Pace (a.coeff b • Q b) from (ht b).const_smul (a.coeff b))];unfold tap;rw [map_sum];apply Finset.sum_eq_zero;intro i _
 rw [flask_scale (ht i)];unfold Q;rw [slurry_prod _ _ (fun j _=>hp _ _),hr,PowerSeries.coeff_smul,PowerSeries.coeff_X_pow_mul',if_neg (by omega),smul_zero]

variable {F :Flake n (Market (Rayk G 2))}{σ p:ℝ}
private def locked (G:Gauge)(n:ℕ) : Coord (n:=n) × Tape n G.ColorIndex ≃ Slide (Rayk G 2) n where
 toFun z:=join z.1 z.2
 invFun x:=((fun i=>((x i).1,(x i).2.1)),(fun i=>(x i).2.2))
 left_inv _:=rfl
 right_inv _:=rfl

-- utility summability
lemma per_okay {I:Type}[Fintype I]{F:Flake n (Market I)}(h:Won F σ p)(he:0≤σ)(v:Vert P I):Summable (fun x:Slide I n=> F x*∑ u:Site P,per_use x v u):=by
 let U (_:Unit):=F
 have hi (u:Site P):Summable (fun x:Slide I n=> F x * per_use x v u) := ((show paidC U σ p from by refine ⟨h.1,?_⟩; simp only [tsum_fintype,Fintype.sum_unique];exact h.2).uses he v u).comp_injective (i:=Prod.mk ()) (fun i j hi=>Prod.mk.inj hi|>.2)
 have hp:=summable_sum (s:=univ) (fun u _=>hi u)
 simpa [Finset.mul_sum] using hp

theorem led (o:Fin n)(h: Cohort F)(he:Held (carpet _) σ p F)(hs:0<σ)(hp:0≤p)(u:Vert P (Rayk G 1)):
 let M:=mass (deposit F o) n
     ; (∑ z:Tape n (Cove P (Rayk G 1)),pour (grown M) o z * ∏ i,u (z i))=
       ∑ z:Tape n (Cove P (Rayk G 2)),pour F o z*∏ i,curling G u (z i):=by
 let η:=σ/(n:ℝ)
 obtain ⟨C,hC,H⟩:=fare G n n (show 0<η from div_pos hs (Nat.cast_pos.mpr o.pos))
 let M:=mass (deposit F o) n
 dsimp only; rw [(H (paid F o hs hp he)).2 P o u]
 simp_rw [at_first, Atom.poly]
 let W:= curling G u
 have ht:=purchased (neck o F) (word_sum (sensible o he hp) hs.le) o W; rw [assumptive o h] at ht
 change _=∑ z:Tape n (Cove P (Rayk G 2)),pour F o z*∏ i,W (z i)
 rw [ht,per_sum,←(locked G n).tsum_eq]
 -- rewrite all on RHS to perm product; summable via per_okay
 have hh:= ((locked G n).summable_iff.mpr (per_okay (sensible o he hp) hs.le W))
 rw [show (∑' z:Coord (n:=n)×Tape n G.ColorIndex, neck o F (locked G n z) *∑ i,per_use (locked G n z) W i)=∑' b:Coord (n:=n),∑' y:Tape n G.ColorIndex,_ from hh.tsum_prod]
 simp_rw [tsum_fintype, Finset.mul_sum];apply tsum_congr;intro x;rw [Finset.sum_comm];apply Finset.sum_congr rfl;intro y _;apply Finset.sum_congr rfl;intro i _
 apply congrArg₂ (·*·) rfl
 unfold per_use;apply Finset.prod_congr rfl;intro j _
 simp only [deposit,slotFace,slot_offset,slot_plaq]
 change (dColor G P 1 (directors G u) (wrap P (x j).1+i,plaqEquiv (plaqEquiv.symm (x j).2))) (y j)=_
 rw [plaqEquiv.apply_symm_apply];rfl
end YM.RG08.Carrel
