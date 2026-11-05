import YM.RG08.Clef.String

/-! # Before/ofer ratio commutation, always through all E. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Clef
open Function Finset Jetty Skiff Lattice Isles Forms Pert.Bulk Filter
open Room Gallery Camera MvPolynomial Glyph Weald Quarry Billet Nacre Steam
open scoped Topology BigOperators PowerSeries Classical Matrix
set_option backward.isDefEq.respectTransparency false
variable {I J:Type}{n e k d l:ℕ}{V:GrainS I}(w:ℕ→ℝ)

def film (V:GrainS I) : GrainS I := fun e n=>∑ i∈range (e+1),Nacre.dues w i n e • V i n
lemma summit_sum (a:J→Pack n I)(S:Finset J)(f:Pearl)(v:Tray I): summit (S.sum a) f v=∑ i∈S,summit (a i) f v:=by
 unfold summit Gallery.volume during; simp_rw [Finset.sum_apply, Finset.sum_smul]; exact Finset.sum_comm
lemma summit_smul (p:ℝ)(F:Pack n I)(f:Pearl)(v:Tray I):summit (p • F) f v=p • summit F f v:=by unfold summit Gallery.volume during;simp [smul_smul, Finset.smul_sum]
lemma summit_blank (f:Pearl)(v:Tray I): summit (0:Pack n I) f v=0:=by simp [summit, Gallery.volume,during]
-- to combine i,n reexpression extend through fixed demand k
-- alignment for actual l slots
private abbrev lan (l e:ℕ):=range (l+e+1)
private abbrev ord (e:ℕ):=range (e+1)
lemma darken (ht:Skiff.Lit l V)(he:e≤k)(f:Pearl)(v:Tray I): crown l V f e v=∑ n∈lan l k,summit (V e n) f v:=Finset.sum_subset (range_mono (by omega)) fun a _ h=>by
   rw [show V e a=0 from Classical.not_not.mp fun hh=>show False from by have :=ht _ _ hh; simp only [mem_range] at h; omega,summit_blank ..]
lemma lit_film (ht:Skiff.Lit l V):Skiff.Lit l (film w V):=by
 intro i n
 contrapose!; intro he; unfold film; apply sum_eq_zero;intro j hj
 rw [show V j n=0 from Classical.not_not.mp (fun hy=>by have hh:=ht _ _ hy; simp only [mem_range] at hj;omega),smul_zero]
lemma cylinder (F:Pack n I)(f:Pearl)(x:Tray I):react w (summit F f (shuttle w x))=(ratio w)⁻¹ ^n * summit F f x:=by
 unfold summit Gallery.volume; rw [map_sum,Finset.mul_sum]; refine sum_congr rfl (fun i _=> ?_)
 rw [_root_.map_smul];change _ • react w (fret (via w x.get) _) = _;rw [frieze, mul_smul_comm] -- maybe wrong orientation
lemma treasure {a e:ℕ}{z:Dig}(ha: a≤e):tap a (∑ j∈ord e, PowerSeries.X^j*(Nacre.dues w k n j • z:Dig))=tap a (PowerSeries.X ^k* (Nacre.shift w k n)* z):=by -- replace shiftR
 let r:= Nacre.shift w k n
 let K:= (PowerSeries.X^k*r:Dig)
 let p(j:ℕ):Dig:=PowerSeries.C (Nacre.dues w k n j)*PowerSeries.X^j
 have he: tap a (K*z)=tap a ((∑ j∈ord e,p j)*z):=by
    refine wired a (fun i hi=>?_) (fun _ _=>rfl)
    unfold p tap; rw [map_sum,sum_eq_single_of_mem i (mem_range.mpr (by omega)) (fun _ _ hi=>by rw [PowerSeries.coeff_C_mul_X_pow,if_neg (Ne.symm hi)])];rw [PowerSeries.coeff_C_mul_X_pow,if_pos rfl,Nacre.beam_dues]
 rw [he,Finset.sum_mul];congr 1;apply sum_congr rfl;intro i _;unfold p;rw [Algebra.smul_def,PowerSeries.algebraMap_apply];simp only [Algebra.algebraMap_self_apply];ac_rfl

lemma pit (ht:Skiff.Lit l V)(e:ℕ)(f:Pearl)(v:Tray I):
    tap e (Weald.mint l (film w V) f v)=tap e (∑ i∈ord e,∑ n∈lan l e,PowerSeries.X^i*Nacre.shift w i n*summit (V i n) f v):=by
 rw [minted l _ _ _ e e le_rfl]
 have hH:(∑ j∈range (e+1), Gpow j (Weald.crown l (film w V) f j v))=∑ j∈ord e,∑ n∈lan l e,∑ i∈ord j, PowerSeries.X^j*(Nacre.dues w i n j • summit (V i n) f v):=by
    apply sum_congr rfl;intro i hi
    unfold Gpow; rw [darken (lit_film w ht) (e:=i) (k:=e) (by simpa using hi) f v, Finset.mul_sum];apply sum_congr rfl;intro j _; unfold film;rw [summit_sum,Finset.mul_sum];apply sum_congr rfl;intro t _;rw [summit_smul]
 let T (i j n:ℕ):Dig:= PowerSeries.X^j*(Nacre.dues w i n j • summit (V i n) f v)
 have hr j (hj:j ∈ ord e) (n:ℕ): (∑ i∈ord j,T i j n)=∑ i∈ord e,T i j n:=sum_subset (range_mono (by simp only [mem_range] at hj;omega)) fun i _ hi=>by unfold T Nacre.dues;simp only [mem_range] at hi;rw [if_neg (by omega),zero_smul,mul_zero]
 rw [hH,Finset.sum_congr rfl (fun j (hj:j∈ord e)=>sum_congr rfl (fun n _=>hr j hj n))]
 have he:(∑ j∈ord e,∑ n∈lan l e,∑ i∈ord e,T i j n)=(∑ i∈ord e,∑ n∈lan l e,∑ j∈ord e,T i j n):=by
    simp_rw [Finset.sum_comm (s:=lan l e) (t:=ord e)];rw [Finset.sum_comm]
 rw [he]; unfold tap; simp_rw [map_sum];apply sum_congr rfl;intro i _;apply sum_congr rfl;intro n _; rw [←map_sum];exact treasure w le_rfl

/-- LITERAL at all coupling degrees; same masks both reps.
 NO g_i power precision loss on repeated terms. -/
lemma rap (ht:Skiff.Lit l V)(x:Tray I)(f:Pearl):
   react w (Weald.mint l V f (shuttle w x))=Weald.mint l (film w V) f x:=by
 ext i:1;change tap i _=tap i _
 rw [gentle w _ _ _ (fun j hj=> minted _ _ _ _ j i hj),pit w ht i f x]
 apply congrArg;rw [map_sum];apply sum_congr rfl;intro j hj
 unfold Gpow;rw [_root_.map_mul,_root_.map_pow,gA_x,darken ht (e:=j) (k:=i) (by simpa using hj) f _,map_sum,Finset.mul_sum];apply sum_congr rfl;intro n _;rw [cylinder,tilt,mul_pow];unfold Nacre.shift;ring!
end YM.RG08.Clef
