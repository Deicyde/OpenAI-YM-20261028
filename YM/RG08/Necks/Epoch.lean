import YM.RG08.Necks.Star
/-! # Shipping variation, including repeated rank n. street on Market export from Ducat.
 Exact sum before output test. Positivity for tally costs.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Necks
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Flint Lagoon Yurt Next.Free
open scoped Classical ContDiff BigOperators Topology ENNReal
variable {I J:Type}{n m d p:ℕ}{σ τ μ V Q B C δ η:ℝ}{L:Jetty.Loom I}{D:Jetty.Loom J}
variable {h:0<σ}{F F':Pack n I}{K K' E₁:Cables n I J}{a:Fin n→ℝ}

def kennel (K:Cables n I J)(F:Pack n I):Pack n J:= Skiff.picture (candles K) (audio n n I J) F
lemma kennel_val (K:Cables n I J)(F:Pack n I)(y:Tape n J)(v:Pearl):kennel K F y v=∑' x,Forms.vat K (fun i=>F i v) y x:=by apply tsum_congr;intro i;exact mul_comm (design K i y) (F i v)
lemma kennel_live (he:Lyrics F)(hs:Sings L d h F B)(hp:Skiff.Parade L D σ E₁ K a):Lyrics (kennel K F)∧ Sings D d h (kennel K F) (B*∏ i,a i):= Skiff.playing he hs (hp.play le_rfl le_rfl)
lemma kennel_sum (he:Lyrics F)(hs:Sings L d h F B)(hp:Skiff.Parade L D σ E₁ K a)(v:Pearl)(y:Tape n J):Summable (Forms.vat K (fun i=>F i v) y):= ((Skiff.showtime he hs (hp.play (k:=h) le_rfl (Nat.le_refl d)) y v).of_norm).congr (fun i=>show design K _ _ * F i v=_ from mul_comm ..)
lemma kennel_linear (he:Lyrics F)(hE:Lyrics F')(hs:Sings L d h F B)(ht:Sings L d h F' C)(hp:Skiff.Parade L D σ E₁ K a):kennel K (F+F')=kennel K F+kennel K F':=by
 funext y v; rw [Pi.add_apply,Pi.add_apply]; simp_rw [kennel_val,←(kennel_sum he hs hp v y).tsum_add (kennel_sum hE ht hp v y)]; apply tsum_congr;intro i;simp only [Forms.vat, Pi.add_apply,add_mul]
lemma kennel_smul (z:ℝ)(K:Cables n I J)(F:Pack n I):kennel K (z • F)=z • kennel K F:=by funext y v;rw [Pi.smul_apply,Pi.smul_apply,smul_eq_mul,kennel_val,kennel_val,←tsum_mul_left];apply tsum_congr;intro i;exact mul_assoc z _ _

-- Frame lengths, Alley anchored aperture when market dimensions target & source.
-- map f:Hearth anonymous, Weight polynomial. street sx common. total card post.
local notation "A"=>Market I
local notation "H"=>Market J
def flare (I J:Type)(s:ℝ):Cables n (Market I) (Market J):=fun _ x y=>s*sep x.1 y.1
lemma flare_geo (x:A)(y:H)(hs:0≤σ):σ*abroad y≤σ*abroad x+σ*sep x.1 y.1:=by
 apply le_trans _ (le_of_eq (mul_add σ _ _));apply mul_le_mul_of_nonneg_left _ hs
 change length y.1≤length x.1+length (x.1-y.1)
 apply le_trans _ (le_of_eq (add_comm (length (x.1-y.1)) _));rw [show length (x.1-y.1)=length (y.1-x.1) from sep_comm ..];nth_rw 1 [← sub_add_cancel y.1 x.1];exact length_add ..
variable {N U:Cables n (Market I) (Market J)}{S T:Pack n (Market I)}
private lemma tracks (hs:0<σ)(hp:street (flare I J σ) N a):Skiff.Parade (stance I) (stance J) σ (flare I J σ) N a:=⟨fun _ _ _ _=>flare_geo _ _ hs.le,fun _ x y=>mul_nonneg hs.le (sep_nonneg x.1 y.1),fun i=>(hp i).1,fun i=>(hp i).2.1⟩
 set_option maxHeartbeats 450000
lemma funnel (hP:Alley (carpet _) (carpet _) σ σ δ C (flare I J σ) N U)(hp:Dyad (stance _) d h B δ S T):Dyad (stance J) d h ((n+1)*B*C^n) δ (kennel N S) (kennel U T):=by
 obtain ⟨hB,hδ,⟨he,hf⟩,hs,ht,hQ⟩:=hp;have hC:= hP.gain
 have hg(i:Fin n):∏ j:Fin n,(if j=i then C*δ else C)=C^n*δ:=by
    rw [←mul_prod_erase _ (fun j=> if j=i then C*δ else C) (mem_univ i),if_pos rfl,prod_eq_pow_card (b:=C) (by intro j hj;exact if_neg (mem_erase.mp hj).1),card_erase_of_mem (mem_univ ..),card_univ,Fintype.card_fin,show C^n=C^(n-1)*C from Eq.symm (by rw [←pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by have :=i.isLt;omega))])];ring
 let V(i:Fin n):=Forms.crossfire N U i
 have hM:=tracks h hP.near;have hN:=tracks h hP.far; have hV(i):=tracks h (hP.street i)
 obtain ⟨h1,H1⟩:=kennel_live he hs hM;obtain ⟨h2,H2⟩:=kennel_live hf ht hN
 rw [prod_const,card_univ,Fintype.card_fin] at H1 H2
 have hi: B*C^n≤((n:ℝ)+1)*B*C^n:=mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hB (by simp)) (by positivity)
 refine ⟨by positivity,hδ,⟨h1,h2⟩,H1.mono le_rfl le_rfl (fun _=>le_rfl) hi,H2.mono le_rfl le_rfl (fun _=>le_rfl) hi,?_⟩ -- missing hδ
 have ha:kennel N S-kennel U T=kennel N (S-T)+∑ i:Fin n,kennel (V i) T:=by
    funext i u;rw [Pi.add_apply,Pi.add_apply,Finset.sum_apply,Finset.sum_apply,Pi.sub_apply,Pi.sub_apply];simp_rw [kennel_val]
    have hu(j):=kennel_sum hf ht (hV j) u i
    rw [←(kennel_sum he hs hM u i).tsum_sub (kennel_sum hf ht hN u i),← Summable.tsum_finsetSum (fun j (_:j∈(univ:Finset (Fin n)))=>hu j),← (kennel_sum (he.sub hf) hQ hM u i).tsum_add (summable_sum (s:=univ) (fun i _=>hu i))]; apply tsum_congr; intro j;exact Forms.firing N U (fun i=>S i u) (fun i=>T i u) i j
 rw [ha]
 let P:ℝ:=B*C^n*δ; have ht':0≤P:=by unfold P;positivity
 have hX:Sings (stance J) d h (kennel N (S-T)) P:=by convert (kennel_live (he.sub hf) hQ hM).2 using 1;simp [P];ring
 have hY:Sings (stance J) d h (∑ i,kennel (V i) T) (∑ _i:Fin n,P):=by
    apply Sings.sum _ _ (fun _ _=>ht') ;intro i _;convert (kennel_live hf ht (hV i)).2 using 1;rw [hg];unfold P;ring -- P folded
 convert hX.add hY ht' (sum_nonneg fun _ _=>ht') using 1; simp [P]; ring
end YM.RG08.Necks
