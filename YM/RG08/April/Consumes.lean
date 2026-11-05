import YM.RG08.April.Fiber
/-! # Resolve the graph recurrence & stencil packets. solver, not a definition.
- specialized Here outputs all physical-scale i in a compatible corridor. Positive-order only; no physical hierarchy label estimates at all. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.April
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Rate.Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Camera Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason
open Function Jetty Lattice Precision Skiff Weald Hatch Planned.PrimaryIntegral295 Labels Source Source.Drops WardBin Parts Atrium Trill Necks Sideshow
open scoped Classical Matrix BigOperators PowerSeries Topology
variable {X:Type}{G:Gauge}{D d p l e n k r:ℕ}
local notation "Δ"=> stance (Loc G 1)
local notation "E"=> Ed G Cover
variable (F:Labels.Frame G d)(W:Rate.Stair X)(H:Housing F W D k)
local notation "I₀"=> Accent F
local notation "V₀"=>Haven W
local notation "R₀"=>Mason.Run W
local notation "D0"=> Mason.kiosk W
local notation "D1"=> Mason.turnstile W
private lemma damp {A q L:ℝ}(_ha:0≤ A)(hq:0≤q)(hL:0<L)(ht:A^2≤L): A*q/L≤ q/Real.sqrt L:=by
 apply (div_le_div_iff₀ hL (Real.sqrt_pos.mpr hL)).mpr
 obtain rfl|hq':=eq_or_lt_of_le hq; · ring_nf;rfl
 have hh:=Real.sq_sqrt hL.le
 have hv:A≤Real.sqrt L:= by nlinarith only [ht,hh,Real.sqrt_nonneg L]
 nlinarith only [mul_le_mul_of_nonneg_right hv (mul_nonneg hq (Real.sqrt_nonneg L)), show Real.sqrt L*Real.sqrt L*q=L*q from by rw [←sq,hh]] -- need hh * q

set_option maxHeartbeats 600000
-- Propagate at stage via rate.Primitive fan, repeat consumes square pre plus nothing across multiple labels.
lemma known_pair (hh:W.Admits)(he:e≤k)(hl:l≤d)(hn:n≤l+e)(hv:Festival F W H e l n):known F W H e l n∧ able F W H e l n:=by
 obtain ⟨B,δ,hB,hδ,HR⟩:=budget F W H hh hv he hl
 obtain ⟨V,hT,hV⟩:=H.vault e n he
 obtain ⟨A,J,hA,hJ,hY⟩:=H.afford e l n he hl hn
 let I:= {i:I₀// octave i=l}
 let K:=Haven W→ I→Pack n E
 let U:K:=fun x i=>H.S x i.val e n;let U':K:=fun x i=>H.S' x i.val e n
 let T:Haven W→ Bool × I→Pack n E:=fun x v=> if v.1 then U x v.2 else U' x v.2
 let Q(i:R₀):=J i*B i^2
 have hQ:(D1).Good Q:=(D1).moreover _ _ hJ (stairs _ hB 2)
 have hhT(i:V₀)(j:I₀): (∃ p:ℝ,0≤p∧Sings Δ D (H.stand i) (H.S i j e n) p)∧(∃ q:ℝ,0≤q∧Sings Δ D (H.stand i) (H.S' i j e n) q):=⟨(H.wish i).1.seats j e he n,(H.wish i).2.seats j e he n⟩
 have hAbs:∃ a,(D0).Good a ∧ ∀ i j,Sings Δ D (H.stand i) (T i j) (a i):=by
    refine drawers (σ:=H.strip) hT hQ ?_ ?_ ?_
    · intro i j;obtain ⟨⟨p,-,hp⟩,q,-,hq⟩:=hhT i j.2;unfold T;split_ifs;exact ⟨_,hp⟩;exact ⟨_,hq⟩
    · intro i hi j;unfold T;split_ifs;exact (hV i hi j.2.val).1;exact (hV i hi j.2.val).2
    intro i t ht hx j
    have hp(c:I): Sings Δ D (H.stand (past W i)) (U (past W i) c) t∧Sings Δ D (H.stand (past W i)) (U' (past W i) c) t:=by
       have h:=hx (true,c);have h':=hx (false,c);simp only [T,ite_true] at h;simp only [T,Bool.false_eq_true,ite_false] at h'; exact ⟨h,h'⟩
    have h:=(hY i).2.2.2 (HR i).1 (HR i).2 ht ht (show 0≤t+t by linarith) (fun j (hj:j∈booth F l)=> by
       obtain ⟨h,h'⟩:=hp ⟨j,(booth_in F).mp hj⟩;exact ⟨h,h',h.sub h' ht ht⟩)
    obtain ⟨h,h'⟩:=h.mint j.2.val ((booth_in F).mpr j.2.property)
    have hW:0<W.length i.x i.m:=by have :=W.length_large i.x i.m; linarith
    have he:A i*t/W.length i.x i.m+Q i ≤ t/Real.sqrt _+Q i:=add_le_add_left (damp ((show 1≤A i from (hY i).1).trans' zero_le_one) ht hW (hY i).2.2.1) _ -- add_left
    unfold T;split_ifs;exact h.mono le_rfl le_rfl (fun _=>le_rfl) he;exact h'.mono le_rfl le_rfl (fun _=>le_rfl) he
 obtain ⟨a,ha,Ho⟩:=hAbs
 have Ho(i c): Sings Δ D (H.stand i) (U i c) (a i)∧Sings Δ D (H.stand i) (U' i c) (a i):=by have h:=Ho i (true,c);have h':=Ho i (false,c);simp [T] at h h';exact ⟨h,h'⟩
 have hnn {i:V₀}:0≤a i:=(D0).safe _ ha _
 let t(i:R₀):=a (past W i);let V(i:R₀):= J i*(B i+t i)^4* δ i
 have ht:(D1).Good t:= (highString hh).golf _ ha
 have ht':(D1).cheap V:= (D1).awe _ _ ((D1).moreover _ _ hJ (stairs _ ((D1).hear _ _ hB ht) _)) hδ
 have hZ(i:R₀)(p:ℝ)(hp:0≤p)(he:∀ j∈Sideshow.booth F l,Sings Δ D (H.stand (past W i)) (H.S (past W i) j e n-H.S' (past W i) j e n) p):=(hY i).2.2.2 (HR i).1 (HR i).2 (B0:=a (past W i)) hnn (B1:=a (past W i)) hnn hp (fun j hj=> by
    obtain ⟨h,h'⟩:=Ho (past W i) (⟨j,(booth_in F).mp hj⟩:I); exact ⟨h,h',he _ hj⟩)
 let R:K:=U-U'; let Q':= V -- oops V shadows p title. top name original V shadow; redo.
 have hVar:∃ c,(D0).cheap c ∧ ∀ i j,Sings Δ D (H.stand i) (R i j) (c i):=by
    apply drawer (q:=a+a) (p:=Q') ((D0).hear _ _ ha ha) ht' (fun k j=>⟨a k+a k,(Ho k j).1.sub (Ho k j).2 hnn hnn⟩) (fun i _ j=> (Ho i j).1.sub (Ho i j).2 hnn hnn)
    intro i u hu hG j
    have hW:0<W.length i.x i.m:=by have :=W.length_large i.x i.m; linarith
    have ht:=(hZ i u hu (by intro j hj;exact hG (⟨j,(booth_in F).mp hj⟩:I))).venue j.val ((booth_in F).mpr j.property)
    exact ht.mono le_rfl le_rfl (fun _=>le_rfl) (add_le_add_left (damp ((show 1≤A i from (hY i).1).trans' zero_le_one) hu hW (hY i).2.2.1) _)
 obtain ⟨c,hc,Hc⟩:=hVar
 refine ⟨fun i hi=>⟨a,c,ha,hc,fun x=>?_⟩,fun i j hi hj=>?_⟩
 · exact ⟨(Ho x (⟨i,hi⟩:I)).1,(Ho x (⟨i,hi⟩:I)).2,Hc x (⟨i,hi⟩:I)⟩
 refine ⟨Q,Q',hQ,ht',fun x=>?_⟩
 have h:=(hZ x (c (past W x)) (tiny _ hc _) (fun i hi=>Hc _ (⟨i,(booth_in F).mp hi⟩:I)))
 obtain ⟨h1,h2⟩:=h.tide;have h3:=h.calm.collects i j hi hj;rw [dusk_diff] at h3
 exact ⟨h1.collects i j hi hj,h2.collects i j hi hj,h3⟩

def merits (d k e l n:ℕ):= (d+k+1)*((d+1)*e+l)+(d+k-n)
lemma merit_order {a b r:ℕ}(hl:l ≤ d)(hn:n≤l+e)(_hA:b ≤ d)(hr:r ≤ b+a)(he:e≤k)(hx:Uptick e l n a b r):merits d k a b r< merits d k e l n:=by
 unfold merits
 rcases hx with hx|⟨rfl,h|⟨rfl,hb⟩⟩;rotate_left 2;omega
 · have heq:(d+1)*a+(b+1)≤(d+1)*e+l:=by have hφ:=Nat.mul_le_mul_left (d+1) hx;rw [Nat.mul_succ] at hφ;omega
   have H:(d+1)*a+b+1≤(d+1)*e+l:=by omega
   have hx:= Nat.mul_le_mul_left (d+k+1) H;rw [Nat.mul_add] at hx;omega
 have H:(d+1)*a+b+1≤(d+1)*a+l:=by omega -- e maybe a
 have hx:= Nat.mul_le_mul_left (d+k+1) H;rw [Nat.mul_add] at hx;omega
/-- **all admitted marks**. This certificate still needs pre constants paid, warmed geometry and boundary.
 Rate depends just on admissible stair guarantees. Eq:kme extraction via merchants at shrinking positive σ, completed interpolation l1 theorem forthcoming. -/
theorem basil (hh:W.Admits)(he:e≤k)(hl:l≤d)(hn:n ≤l+e):known F W H e l n ∧ able F W H e l n:=by
 generalize hx: merits d k e l n = i
 induction i using Nat.strong_induction_on generalizing e l n with
 | h i ih=>
   have ho (a b r:ℕ)(ha:a ≤ k)(hb:b ≤ d)(hp:r ≤ b+a)(hr: Uptick e l n a b r):=ih _ (hx ▸ merit_order hl hn hb hp he hr) ha hb hp rfl
   exact known_pair F W H hh he hl hn ⟨fun a b r ha hb hp hr=>(ho a b r ha hb hp hr).1,fun a b r ha hb hp hr=>(ho a b r ha hb hp hr).2⟩
lemma pillar (hh:W.Admits)(i:I₀)(he:e≤k):Blue D0 D H.strip H.stand (fun j=>H.S j i e n) (fun j=>H.S' j i e n):=by
 by_cases hy:n≤octave i+e; · exact (basil F W H hh he (octave_le i) hy).1 i rfl
 have hN(j:V₀): H.S j i e n=0∧H.S' j i e n=0:=⟨Classical.not_not.mp (fun h=>hy (((H.wish _).1.unbound _).inlet.lit _ _ h)),Classical.not_not.mp (fun h=>hy (((H.wish _).2.unbound _).inlet.lit _ _ h))⟩
 rw [funext (fun j=>(hN j).1), funext (fun j=>(hN j).2)];exact blue_zero
lemma seraph (hh:W.Admits)(i j:I₀)(he:e≤k):Oil D1 (fun x=>tap e (H.P x j i)) (fun x=>tap e (H.P' x j i)):= (basil F W H hh he (octave_le i) (Nat.zero_le _)).2 _ _ rfl (Nat.zero_le _)
end YM.RG08.April
