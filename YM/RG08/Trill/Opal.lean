import YM.RG08.Trill.Perc
/-! # Single-order bracket on an arbitrary tested horizon & exponential-width packet.
Calculated as ordinary coefficient in radial variables first, then engineering read via Bigrade.
No continuation of the log in far-off columns. Own-g convention; by rank. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Trill
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Skiff Trickle
open Room Gallery Camera MvPolynomial Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Flint
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts
open scoped Classical ContDiff BigOperators Topology ENNReal Matrix.Norms.Frobenius
variable {G:Gauge}{d n p l e D:ℕ}
local notation "E"=>Ed G Cover
local notation "Y"=>Snap G d
abbrev Gras (G:Gauge)(n:ℕ):=Pack n (Ed G Cover)
/-- Takes all allocations through factor count p. Eng grade via Parts.capture. -/
def grants (F:Gras G n)(f:Pearl)(p d:ℕ)(X:Snap G d) :ℝ:=∑ a: Fin n→Fin (p+1) with ∑ i,(a i).val=p, sonic F f (fun i=>pluck (a i).val X)
lemma grants_scale (F:Gras G n)(f:Pearl)(s:ℝ)(X:Y) : grants F f p d (s • X)=s^p • grants F f p d X:=by
 unfold grants;rw [smul_eq_mul,mul_sum];apply sum_congr rfl;intro i hi
 simp_rw [pluck_scale,sonic_pull,prod_pow_eq_pow_sum,(mem_filter.mp hi).2]

lemma grants_abba (F:Gras G n)(f:Pearl)(X:Y)(hl:p<n) : grants F f p d X=0:=by
 unfold grants;apply Finset.sum_eq_zero;intro i hi
 suffices h:∃ k,(i k).val=0 by
    obtain ⟨k,hk⟩:=h; apply sonic_zero (i:=k) (X:=fun k=>pluck (i k).val X) _ f;rw [hk,pluck_zero]
 by_contra! hz;have hh: n≤∑ k,(i k).val:= by simpa using Finset.sum_le_sum (s:=univ) (f:=fun (_:Fin n)=>1) (g:=fun j=>(i j).val) (fun j _=>Nat.one_le_iff_ne_zero.mpr (hz j))
 rw [(mem_filter.mp hi).2] at hh;exact (not_lt_of_ge hh) hl

lemma grants_edge (F:Gras G n)(f:Pearl)(X:Y): grants F f n d X=sonic F f (fun _=>pluck 1 X):=by
 -- unique allocation, including n=0
 let u(i:Fin n):Fin (n+1):=⟨1,by have :=i.isLt;omega⟩
 unfold grants;rw [sum_eq_single u]
 · intro i hi hu;have hh:= (mem_filter.mp hi).2
   have hz:∃ k,(i k).val=0:=by
     by_contra! ht
     have hr(k): (i k).val=1:=le_antisymm (by
       by_contra! Ht
       have hv:n<(∑ j:Fin n,(i j).val):=by simpa using Finset.sum_lt_sum (s:=univ) (f:=fun (_:Fin n)=>1) (g:=fun j=>(i j).val) (fun j _=> Nat.one_le_iff_ne_zero.mpr (ht j)) ⟨k,mem_univ _,Ht⟩
       rw [hh] at hv;omega) (Nat.one_le_iff_ne_zero.mpr (ht k))
     exact hu (funext fun k=>Fin.ext (hr k))
   obtain ⟨k,hk⟩:=hz; apply sonic_zero (i:=k) (X:=fun i'=>pluck (i i').val X) _ f;rw [hk,pluck_zero]
 intro h;exact (h ((mem_filter.mpr ⟨mem_univ _,by simp [u]⟩))).elim
variable {F:Gras G n}{P:GrainS (Ed G Cover)}
lemma grants_cast (hc:Calls l P)(hp:Permit D l P)(H:Hol G)(u:G.El)(f:Pearl)(X:Y): grants (P e n) f p d (Drops.Cast u X)=grants (P e n) f p d X:=by
 unfold grants;apply sum_congr rfl;intro i hi
 simp_rw [pluck_cast H]
 choose C hC B using key_budget G d
 exact holy hc hp u f (fun k=>C (i k).val* ∏ _j:Fin (i k).val,‖X‖) _ (p:=d*p) (fun k=>(B _ (fun _=>X)).here le_rfl (Nat.mul_le_mul_left _ (Nat.le_of_lt_succ (i k).isLt)))

-- sonic bill variant for dependent finite alphabets.
variable {σ B:ℝ}{g:0<σ}
lemma g_bill {J:Fin n→Type}[∀ i,Fintype (J i)](he:Lyrics F)(hh:Sings (stance _) D g F B)(hb:0≤B)(f:Pearl){a:(i:Fin n)→J i→ℝ}{X:(i:Fin n)→J i→E→ℝ}(hz:∀ i j,Bearing (stance _) p 0 (a i j) (X i j)):
 sonic F f (fun j=>∑ i:J j,X j i)=∑ t:(j:Fin n)→J j,sonic F f (fun i=>X i (t i)):=by
 unfold sonic tote flakes;simp_rw [Finset.sum_apply];simp_rw [Fintype.prod_sum]
 simp_rw [mul_sum]
 rw [Summable.tsum_finsetSum (f:=fun (t:(j:Fin n)→J j) (x:Tape n E)=>F x f*∏ i:Fin n,X i (t i) (x i)) (fun t _=> (sonic_abs he hh hb f (a:=fun i=>a i (t i)) (V:=fun i=>X i (t i)) (le_rfl:(0:ℝ)≤0) (by rw [mul_zero];exact (half_pos g).le) (fun i=>hz ..)).of_norm)]

-- apply FDsnap real basis to each m-lane
abbrev Joss (G:Gauge)(d:ℕ):=Fin (Module.finrank ℝ (Snap G d))
 set_option synthInstance.maxHeartbeats 300000
abbrev cello (G:Gauge)(d:ℕ):Module.Basis (Joss G d) ℝ (Snap G d):=Module.finBasis ℝ (Snap G d)
def ray (G:Gauge)(d:ℕ)(i:Joss G d):Snap G d→L[ℝ]ℝ:= (LinearMap.toContinuousLinearMap) ((cello G d).coord i)
lemma ray_sum (z : Y): ∑ i:Joss G d, ray G d i z • cello G d i = z :=(cello G d).sum_repr z

def coral (t:Tape p (Joss G d))(X:Y):=∏ j, ray G d (t j) X
def notch (t:Tape p (Joss G d)):E→ℝ:=fun i=>keytar i p (cello G d ∘ t)
lemma ray_expand (X:Y)(p:ℕ) : pluck p X=∑ t:Tape p (Joss G d),coral t X • notch t:=by
 funext s
 let M:= @keytar G d s p
 change M (fun _=>X)=(∑ t:Tape p (Joss G d),coral t X • notch t) s
 have he:M (fun _=>X)=M (fun _=>∑ i:Joss G d, ray G d i X • cello G d i):=by rw [ray_sum X]
 rw [he,M.map_sum (fun _ i=> ray G d i X • cello G d i),Finset.sum_apply];apply sum_congr rfl; intro i _;rw [M.map_smul_univ];rfl
lemma solos_serve {C:ℕ}(he:Lyrics F)(hh:Sings (stance _) D g F B)(hb:0≤B)(f:Pearl)(a:Fin n→Fin (C+1))(X:Y) :
 sonic F f (fun j=>pluck (a j).val X)=∑ t:(j:Fin n)→Tape (a j).val (Joss G d),(∏ i, coral (t i) X)* sonic F f (fun i=> notch (t i)):=by
 simp_rw [ray_expand]
 choose D hD H using key_budget G d
 let u (i:Fin n)(t:Tape (a i).val (Joss G d)):=D (a i).val * ∏ k:Fin (a i).val,‖cello G d (t k)‖
 have hv(i:Fin n)(t:Tape (a i).val (Joss G d)): Bearing (stance _) (d*C) 0 (u i t) (notch t):=(H _ (cello G d ∘ t)).here le_rfl (Nat.mul_le_mul_left d (Nat.le_of_lt_succ (a i).isLt))
 rw [g_bill he hh hb f (a:=fun i t=> |coral t X| * u i t) (fun i t=>(hv i t).smul (coral t X))];simp_rw [sonic_pull]
lemma grants_smooth (he:Lyrics F)(hh:Sings (stance _) D g F B)(hb:0≤B)(f:Pearl) : ContDiff ℝ ω (grants F f p d):=by
 unfold grants;apply ContDiff.sum -- likely
 intro i hi
 simp_rw [solos_serve he hh hb f]; apply ContDiff.sum
 intro t _;unfold coral;apply ContDiff.mul _ contDiff_const; refine contDiff_prod (fun j (_:j∈(univ:Finset (Fin n)))=>?_); exact contDiff_prod (fun k _=> (ray G d (t j k)).contDiff)
/-- field h label-valued contribution at engineering k & factor p. -/
def synth (F:Gras G n)(f:Pearl)(p d:ℕ)(X:Snap G d):ℂ:= grants F f p d X
 set_option maxHeartbeats 800000
lemma synth_safe (hc:Calls l P)(hp:Permit D l P)(H:Hol G)(f:Pearl):Parts.Safe (synth (P e n) f p d):=by
 obtain ⟨σ,hσ,T,hT,hT'⟩:= (hp.price e n).2
 refine ⟨(Complex.ofRealCLM.contDiff.comp (grants_smooth (hp.price e n).1 hT' hT f)).contDiffAt.of_le le_top,fun u=>Filter.Eventually.of_forall (fun v=>?_ )⟩
 unfold Function.comp synth; rw [grants_cast hc hp H]
end YM.RG08.Trill
