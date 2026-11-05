import YM.MultipleContact.Matching.Spacing
import YM.MultipleContact.Bunch.Focal
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Bunching
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Extra.Histories Extra.Trajectories Cells MergeProof MergeProof.Ribbons
open YM.Next.Rank.Station MergeProof.Accent
open Push.Local YM.Extra.Multi YM.Push.GridApprox.Nil YM.Next.Rank YM.Next.Rank.Spindle YM.PhysicalNext.Repeat.Lotus Merge
open scoped Topology BigOperators Classical
section
variable {α:Type}[Fintype α][Inhabited α][DecidableEq α]{G:Gauge} (C:Family G) (J j p k:ℕ)(q:Side)
set_option quotPrecheck false
local notation "V'"=> Site (C.side J p)
local notation "E"=> YM.Mix.camp C p J
local notation "Rb"=> C.path.levels.budget
variable (a:α→Site (C.side j p))
local notation "t"=> (Rb k).B
local notation "W"=> fuga C.path.levels k
local notation "v"=> loops C j p

def marks (i:ℕ) (x:BatchRibbon.Name (Site (C.side J p)) α) : Site (C.side i p) := bites C J j p (a x.2) i (x.1,true)
local notation "o"=> marks C J j p a
lemma marks_center (i)(ha:a default=0)(x:V'):o i (x,default)=E i x:=by
   have h: loops C j p (a default) i=0:=by
      rw [ha]; unfold loops; split
      next he=> exact (C.S.toDepth he p).root.map_zero
      next he=> have hk' : (C.S.toDepth (Nat.le_of_lt (Nat.lt_of_not_ge he)) p).root 0=0:= (C.S.toDepth _ p).root.map_zero
                exact hk' ▸ (Ratio.embed_parent _ _)
   simp only [marks,Prod.snd,Prod.fst,bites,ite_true,h,affine,Signed.act_zero,zero_add,add_zero]
lemma ascending (hk:J≤j)(n:ℕ): Migrating C.path j p n o:=by
   refine ⟨fun i hj hn=> funext fun x => ?_⟩; exact congr_fun ((retina C J j p n (a x.2) hk).mare i hj hn) (x.1,true)
lemma groups (μ:ℕ)(hk:J ≤ k)(hm:k≤μ)(hi:μ≤j): (C.S.toDepth hm p).parent ∘ o μ=o k:=by
    funext x; exact congr_fun (bitesParent C J j p k (a x.2) hk hm hi) (x.1,true)
private lemma sep_sub (n:Side)(x y : Site n): separation x y=separation (x-y) 0:=by
   rw [← separation_translate x y (-y)]; simp [sub_eq_add_neg]
lemma loops_upper (a:Site (C.side j p))(hk:k≤j)(hh:‖C.S.place a‖ ≤4*Matching.topZone C.path.levels q k) : separation (loops C j p a k) 0 ≤ Matching.patch C.path.levels q k :=by
    let Z:= C.S.toDepth hk p; let B:= separation (loops C j p a k) 0; let c:= Z.count.val; let y:= C.S.place a
    have hV: 2*separation a (Z.embed (loops C j p a k))< c:= (by rw [vote C _ _ _ _ hk]; exact Station.midway _ (C.S.toDepth_odd hk p) _)
    have hz : separation (Z.embed (loops C j p a k)) 0 = c*B:=by nth_rw 1 [show _= loops C j p a k from rfl]; nth_rw 1 [show (0:Site (C.side j p))=Z.embed 0 from Z.root.map_zero.symm]; exact Station.both ..
    have hq:= separation_triangle (Z.embed (loops C j p a k)) a 0; rw [separation_comm (Z.embed _) a,hz] at hq
    have hy : C.S.a j*c=C.S.a k:= C.S.embeds_scale Z; have ha₀:= C.S.a_pos j; have hp':= C.S.a_pos k; have hb:1 ≤ ((t:ℕ):ℝ):=by exact_mod_cast (Rb k).B_pos
    obtain ⟨h₁,-⟩:= normC C j p a
    have hR: C.S.a k*B ≤ C.S.a k+‖y‖:= by
       rw [← hy,mul_assoc]; have hx: ((c*B:ℕ):ℝ)≤ c+(separation a 0:ℝ):= by exact_mod_cast (show c*B≤ c+separation a 0 by omega)
       rw [Nat.cast_mul] at hx; exact (mul_le_mul_of_nonneg_left hx ha₀.le).trans (by rw [mul_add]; linarith only [h₁])
    show separation (loops C j p a k) 0 ≤1024*q.val*t*t
    suffices hu:(B:ℝ) ≤1024*q.val*(t:ℝ)*(t:ℝ) by exact_mod_cast hu
    have hC : (B:ℝ)≤ 1+512*(t:ℝ)^2*q.val:= by
        apply le_of_mul_le_mul_left (a:=C.S.a k) _ hp'; change ‖y‖ ≤4*((q.val:ℝ)*(128*((t:ℕ):ℝ)^2*C.S.a k)) at hh; linarith only [hR,hh]
    have hx:1≤ (q.val:ℝ):=by exact_mod_cast q.pos
    have hv:= mul_le_mul_of_nonneg_right hx (sq_nonneg (↑(t):ℝ)); change (B:ℝ) ≤ _; nlinarith only [hC,hb,hv]
lemma wide_gap (hk:k≤j)(hp:∀ b c:α,b≠c→ W/16≤ ‖C.S.place (a b - a c)‖) :
    ∀b c:α, b≠c→t^2+1 ≤ separation (v (a b) k) (v (a c) k):=by
    intro b c hc; obtain ⟨-,h₂⟩:= normC C j p (a b - a c)
    let Z:= C.S.toDepth hk p; let B:= separation (v (a b) k) (v (a c) k); let n:= Z.count.val
    have hV i: 2*separation (a i) (Z.embed (v (a i) k))< n:= (by rw [vote C _ _ _ _ hk]; exact Station.midway _ (C.S.toDepth_odd hk p) _)
    have hz : separation (Z.embed (v (a b) k)) (Z.embed (v (a c) k)) = n*B:= Station.both ..
    have hM: separation (a b - a c) 0 ≤ B*n+n:=by
        have hL:= separation_triangle (a b) (Z.embed (v (a b) k)) (Z.embed (v (a c) k))
        have hR:= separation_triangle (a b) (Z.embed (v (a c) k)) (a c); rw [hz] at hL; rw [separation_comm (Z.embed _) (a c)] at hR
        rw [← sep_sub,mul_comm B]; have hN:= hV b; have hC:=hV c; unfold n at *; omega
    have hy : C.S.a j*n=C.S.a k:= C.S.embeds_scale Z; have ha:= C.S.a_pos j; have hp':= C.S.a_pos k; have hb:1 ≤ ((t:ℕ):ℝ):=by exact_mod_cast (Rb k).B_pos
    have hs: C.S.a j*(separation (a b -a c) 0:ℝ) ≤ C.S.a k*(B+1:ℝ):=by
         rw [← hy]; refine (mul_le_mul_of_nonneg_left (show (separation (a b-a c) 0:ℝ)≤ ((B*n+n:ℕ):ℝ) from (by exact_mod_cast hM)) ha.le).trans_eq (by push_cast; ring)
    have hv : (128*(t:ℝ)^2*C.S.a k)/16 ≤ 2*(C.S.a k*(B+1:ℝ)):= (hp b c hc).trans (h₂.trans (le_trans (le_of_eq (mul_assoc ..)) (mul_le_mul_of_nonneg_left hs zero_le_two)))
    have ht:8*((t:ℕ):ℝ)^2 ≤ 2*((B:ℝ)+1):= by apply le_of_mul_le_mul_right (a:=C.S.a k) _ hp'; linarith only [hv]
    exact_mod_cast (show ((t:ℕ):ℝ)^2+1≤ (B:ℝ) from by nlinarith only [ht,hb])
lemma already_exist {n X:ℕ} (hk:J ≤ k)(hp:∀ b c,b≠c→n+1≤ separation (v (a b) k) (v (a c) k))(hv:∀b,separation (v (a b) k) 0≤ X)(hX:n+1+2*X ≤ (C.S.toDepth hk p).count.val):∀ (i j':BatchRibbon.Name V' α),i≠j'→ n+1 ≤ separation (o k i) (o k j'):=by
    rintro ⟨i,b⟩ ⟨j',c⟩ h; by_cases hi:i=j'; subst i
    · have hf:b ≠ c:=fun htq=> h (htq ▸ rfl); change n+1≤ separation (bites C J j p (a b) k (j',true)) (bites C J j p (a c) k (j',true)); unfold bites; simp [affine,hands,separation_signed,separation_translate,(hp b c hf)]
    have ht:(C.S.toDepth hk p).count.val ≤ separation (E k i) (E k j'):=by simp_rw [elev C J p k hk,Station.both]; exact Nat.le_mul_of_pos_right _ (separation_pos _ _ hi)
    have hx: separation (o k (i,b)) (E k i)≤X:=(reachBit C J j p k (a b) hk i true).trans (hv _)
    have hL: separation (o k (j',c)) (E k j')≤X:=(reachBit C J j p k (a c) hk j' true).trans (hv _)
    have h₁:=separation_triangle (E k i) (o k (i,b)) (o k (j',c)); have h₂:=separation_triangle (E k i) (o k (j',c)) (E k j'); rw [separation_comm _ (o k (i,b))] at h₁; omega
lemma spaced {X:ℕ} {δ φ:ℕ→ℝ} (h:Brine C.path k δ φ)(hk:J ≤ k)(hp:∀b c,b≠c→t^2+1≤ separation (v (a b) k) (v (a c) k))(hv:∀b,separation (v (a b) k) 0 ≤ X)(hX:t^2+1+2*X ≤ (C.S.toDepth hk p).count.val):∀ i,k ≤ i→i≤j→ Edition.Spaced (Rb i).B (o i):=by
    have hY:=already_exist C J j p k a hk hp hv hX; intro i hi he s u hΔ; have hh:=(groups C J j p k a i hk hi he)
    let T:= C.S.toDepth hi p; let L:=T.count.val; have hx(x): 2*separation (o i x) (T.embed (o k x))< L:=by rw [← hh]; exact Station.midway T (C.S.toDepth_odd hi p) _
    have ht:L*(t^2+1) ≤ separation (T.embed (o k s)) (T.embed (o k u)):=by rw [Station.both]; exact Nat.mul_le_mul_left _ (hY s u hΔ)
    have hh₁:= separation_triangle (T.embed (o k s)) (o i s) (T.embed (o k u)); have hh₂:=separation_triangle (o i s) (o i u) (T.embed (o k u)); rw [separation_comm (T.embed (o k s)) (o i s)] at hh₁
    have he':(Rb i).B^2 ≤ L*t^2:=gap_comp C p k i h hi; have hh₃:=hx s; have hh₄:=hx u; rw [mul_add,mul_one] at ht; omega
lemma cover {d':ℕ}(he:J ≤ k)(hp:∀b,separation (v (a b) k) 0 ≤ d'*t): ∀ i:V',coverNumber t (univ.image fun b=>o k (i,b)) ≤ (2*d'+1)^4:=by
    intro i; have hh:= Corona.tile (E k i) d' t (Rb k|>.B_pos)
    refine (Corona.cover_mono (show (univ.image fun b=>o k (i,b))⊆ halo (d'*t) {E k i} from ?_) t).trans ?_
    · intro x h; obtain ⟨b,hb,rfl⟩:= mem_image.mp h; exact halo_spec.mpr ⟨E k i,mem_singleton_self _,separation_comm .. ▸ ((reachBit C J j p k (a b) he i true).trans (hp b))⟩
    simpa only [two_mul] using hh
end
end YM.MultipleContact.Bunching
