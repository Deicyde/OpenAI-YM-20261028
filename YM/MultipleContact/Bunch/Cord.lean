import YM.MultipleContact.Bunch.Outer
import Mathlib.Data.Finset.Sort
import YM.MergeProof.West.Fur
/-! Interpolation on a finite product, with separate addresses avoiding all prior coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Bunching.Cord
open Filter Set Function Lattice YM.MergeProof YM.MergeProof.Acme
open scoped Classical BigOperators Topology

def radius (n D:ℕ):ℝ:=4*(((2^D+n:ℕ):ℝ)+2)
lemma radius_pos (n D:ℕ):0<radius n D:=by unfold radius; positivity
def streak (i:Axis)(x:E4)(a t:ℝ):= Ward.inc i x (t*a)

private lemma nodes (n D:ℕ)(x:E4)(s:Axis)(u:Fin n→ℝ)(a:ℝ)(ha:0<a):
    ∃ p:Fin (2^D)→ℝ, arced D (radius n D) p ∧ ∀ i, (∃ v:ℤ, streak s x a (p i) s=a*v) ∧ ∀ j,streak s x a (p i) s ≠ u j:=by
   let w:=x s/a; let N:=2^D+n; let r:= ⌊w⌋
   have hr: (r:ℝ)≤ w:=Int.floor_le w
   have he:w< (r:ℝ)+1:=Int.lt_floor_add_one _
   have hw:a*w=x s:=mul_div_cancel₀ _ ha.ne'
   let v (i:Fin N):ℤ:= r+i.val
   let M (i:Fin N):= a * (v i:ℝ)
   let vals:= Finset.univ.image u
   let bad:= Finset.univ.filter fun i=>M i∈vals
   let R:= Finset.univ \ bad
   have hi : Injective M:=by
      refine fun i j h=>Fin.ext ?_; simp only [M,v,Int.cast_add,Int.cast_natCast] at h
      exact_mod_cast (show ((i.val:ℕ):ℝ)=↑j.val from by linarith only [(mul_right_injective₀ ha.ne' h)])
   have hc : 2^D ≤ R.card:=by
      have hy: bad.card ≤ vals.card:= (Finset.card_image_of_injective bad hi) ▸ Finset.card_le_card (Finset.image_subset_iff.mpr fun _ h=> Finset.mem_filter.mp h|>.2) -- direction?
      have hf: vals.card ≤ n:=by simpa only [Fintype.card_fin,Finset.card_univ] using Finset.card_image_le (f:=u) (s:=Finset.univ)
      have hx:bad.card+R.card=N:=by unfold R; rw [Nat.add_comm,Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin]
      omega
   let f:= R.orderEmbOfCardLe hc
   have hf j: (f j).val < N:= Fin.isLt _
   let rp i:=(v (f i):ℝ)-w
   have hp i: streak s x a (rp i) s= M (f i):=by unfold M streak Ward.inc rp; simp [basis_eq,← hw]; ring
   refine ⟨rp, ⟨fun i=>?_,fun i j h=>?_⟩, fun i=>⟨⟨_, hp i⟩,fun j e=>?_⟩⟩
   · dsimp [rp,v]; push_cast; have hj: (↑(f i).val:ℝ)< N:=by exact_mod_cast hf i
     have hn : (0:ℝ)≤(f i).val:=by exact_mod_cast Nat.zero_le (f i).val
     unfold radius; change _∈ Icc (-(4*((N:ℝ)+2))) _; constructor <;> linarith only [hr,he,hj,hn]
   · have hj:(↑(f i).val:ℝ)+1≤ ↑(f j).val:=by exact_mod_cast (show (f i).val+1 ≤ (f j).val from f.strictMono h)
     dsimp only [rp,v]; push_cast; linarith only [hj]
   have he: f i∈bad:= Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,e.symm.trans (hp i)⟩⟩
   exact (Finset.mem_sdiff.mp (R.orderEmbOfCardLe_mem hc i)).2 he
private lemma norm_shift {p:ℝ}{j:Axis}{t:ℝ}(h:0 ≤ p)(x:E4)(a:ℝ) (ha:0 < a)(hv:t∈ Icc (-p) p): ‖streak j x a t-x‖≤p*a:=rink h x a ha hv -- rink Acme?
private lemma keep {j i:Axis}{x:E4}(h:j≠i)(v t:ℝ): streak i x v t j=x j:=by simp [streak,Ward.inc,h]

def Near (n:ℕ)[Inhabited (Fin n)](L:Lattice.Side)(r:ℝ)(y:Fin n→E4):Prop:= y default=0 ∧ (∀s t,s≠t→ r/4<‖y s-y t‖) ∧ ∀s, ‖y s‖<2*L.val * r
def Band (n:ℕ)[Inhabited (Fin n)](L:Lattice.Side)(r:ℝ)(y:Fin n→E4):Prop:= y default=0 ∧ (∀s t,s≠t→ r/16<‖y s-y t‖) ∧ ∀s, ‖y s‖<4*L.val * r
def polar {n:ℕ}(i:Fin n×Axis)(x:Fin n → E4)(a t:ℝ):Fin n→E4 := Function.update x i.1 (streak i.2 (x i.1) a t)
lemma polar_zero {n:ℕ}(i:Fin n×Axis)(x:Fin n→E4)(a:ℝ):polar i x a 0=x:=by unfold polar; simp only [streak,Ward.inc]; simp

def tolerates (n:ℕ)(r:ℝ):ℝ:= r/(16*((8*n:ℕ)+1:ℝ))
lemma tolerates_le (n:ℕ){r:ℝ}(hr:0<r): 0<tolerates n r∧tolerates n r≤r/16:=by unfold tolerates; push_cast; exact ⟨by positivity,by gcongr; have : 0 ≤ (n:ℝ):=Nat.cast_nonneg _; linarith⟩
private lemma within {L:Lattice.Side}{n D:ℕ}[Inhabited (Fin n)]{i:Fin n×Axis}(hi:i.1≠default){r a:ℝ}(hr:0<r)(ha:0<a) (hf:radius n D*a≤tolerates n r) {x y:Fin n→E4} (h:Near n L r y) (h0:x default=0)(hz: ∀s,‖x s-y s‖≤r/16): ∀ t∈Icc (-radius n D) (radius n D),Band n L r (polar i x a t):=by
    intro t ht; have hf'(s):‖polar i x a t s-y s‖≤r/8:=by
        have hx:= (norm_shift (j:=i.2) (radius_pos _ _).le (x i.1) a ha ht).trans hf; have he:= tolerates_le n hr|>.2
        unfold polar; by_cases h:s=i.1
        · subst s; rw [Function.update_self]; linarith only [norm_sub_le_norm_sub_add_norm_sub (streak i.2 (x i.1) a t) (x i.1) (y i.1),hx,hz i.1,he]
        rw [Function.update_of_ne h]; linarith only [hz s,hr]
    refine ⟨show Function.update _ _ _ default=0 from (Function.update_of_ne (Ne.symm hi) ..).trans h0,fun s u hsu=>?_,fun s=> ?_⟩
    · skip -- using r/8+r/8= r/4, no positive gain! need tolerance 1/32 and allowed accumulated r/32.
      have hR(s):‖polar i x a t s-y s‖ ≤ r/16 + tolerates n r:=by
        have hx:= (norm_shift (j:=i.2) ((radius_pos ..).le) (x i.1) a ha ht).trans hf
        unfold polar; by_cases hs:s=i.1
        · subst s; rw [Function.update_self]; linarith only [norm_sub_le_norm_sub_add_norm_sub (streak i.2 (x i.1) a t) (x i.1) (y i.1),hx,hz i.1]
        rw [Function.update_of_ne hs]; exact (hz s).trans (le_add_of_nonneg_right (tolerates_le n hr).1.le)
      have hn :0<n:= Fin.pos i.1
      have he:tolerates n r ≤ r/32:=by apply div_le_div_of_nonneg_left hr.le (by norm_num); push_cast; exact_mod_cast (show 32≤16*(8*n+1) from by omega)
      linarith only [h.2.1 s u hsu,hR s,hR u, norm_sub_le_norm_sub_add_norm_sub (y s) (polar i x a t s) (y u), norm_sub_le_norm_sub_add_norm_sub (polar i x a t s) (polar i x a t u) (y u),he,norm_sub_rev (y s) (polar i x a t s)]
    have hu:1≤(L.val:ℝ):=by exact_mod_cast L.pos
    nlinarith only [hu,hr,h.2.2 s,hf' s,(show ‖polar i x a t s‖≤‖polar i x a t s-y s‖+‖y s‖ by nth_rw 1 [← sub_add_cancel (polar i x a t s) (y s)]; exact norm_add_le ..),mul_le_mul_of_nonneg_right hu hr.le]

def Placed (n:ℕ)[Inhabited (Fin n)](a:ℝ)(x:Fin n→E4)(i:Fin n×Axis):Prop:= i.1≠default → (∃v:ℤ,x i.1 i.2=a*v) ∧ ∀ s, s≠i.1 → x i.1 i.2≠ x s i.2
open Finset
set_option maxHeartbeats 9000000
lemma sample (L:Lattice.Side)(D n:ℕ)[Inhabited (Fin n)]:∃ P> (0:ℝ),∀ (r a ε:ℝ),0<a→0<ε→0<r→ radius n D * a ≤ tolerates n r → ∀ f:(Fin n→E4)→ℂ,
     (∀x:Fin n→E4,Band n L r x → (∀i,Placed n a x i)→ ‖f x‖≤ε) →
     (∀ (i:Fin n×Axis),i.1≠default → ∀ x:Fin n→E4,(∀t∈Icc (-radius n D) (radius n D), Band n L r (polar i x a t))→
         ∃ z:ℕ→ℝ→ℂ, z 0=f ∘ polar i x a ∧ (∀k<D,∀t∈Icc (-radius n D) (radius n D), HasDerivAt (z k) (z (k+1) t) t) ∧ (∀t∈Icc (-radius n D) (radius n D), ‖z D t‖≤ ε))→
     ∀x,Near n L r x → ‖f x‖≤ε*P:=by
    obtain ⟨A,hA,H⟩:=angel D _ (radius_pos n D); refine ⟨(1+A)^Fintype.card (Fin n×Axis),pow_pos (by linarith) _,fun r a ε ha he hr hf f hnodes heads y hy=>?_⟩
    let p':= tolerates n r
    have ht(K:Finset (Fin n × Axis))(hK: ∀ i∈K,i.1≠default)(x:Fin n→E4)(h0:x default=0) (hx:∀ s,‖x s-y s‖+(K.card:ℝ) * p'≤ r/16)(hb: ∀ i∉K,Placed n a x i): ‖f x‖ ≤ ε*(1+A)^K.card:=by
        induction K using Finset.induction_on generalizing x with
        | empty => simp only [Finset.card_empty,pow_zero,mul_one]; apply hnodes x ⟨h0,fun s u hsu=>?_, fun s=> ?_⟩ fun i=>hb i (by simp)
                   · simp only [Finset.card_empty,Nat.cast_zero,zero_mul, add_zero] at hx; linarith only [hy.2.1 s u hsu,norm_sub_le_norm_sub_add_norm_sub (y s) (x s) (y u),norm_sub_le_norm_sub_add_norm_sub (x s) (x u) (y u),hx s,hx u,hr, norm_sub_rev (y s) (x s)]
                   have hu:1≤(L.val:ℝ):=by exact_mod_cast L.pos
                   simp only [Finset.card_empty,Nat.cast_zero,zero_mul,add_zero] at hx; nlinarith only [hu,hr,hy.2.2 s,hx s,(show ‖x s‖ ≤ ‖x s-y s‖+‖y s‖ by nth_rw 1 [← sub_add_cancel (x s) (y s)]; exact norm_add_le ..), mul_le_mul_of_nonneg_right hu hr.le]
        | @insert i K hi ih =>
          have hle(s):‖x s-y s‖≤r/16:=(le_add_of_nonneg_right (mul_nonneg (show 0≤ ((insert i K).card:ℝ) from Nat.cast_nonneg _) ((tolerates_le n hr).1.le))).trans (hx s)
          have hstep:= within (i:=i) (hK i (Finset.mem_insert_self ..)) hr ha hf hy h0 hle
          obtain ⟨z,hz,h₁,h₂⟩:=heads i (hK i (Finset.mem_insert_self ..)) x hstep
          obtain ⟨w,hw,hW⟩:= nodes n D (x i.1) i.2 (fun j=>x j i.2) a ha
          have hε: ε ≤ ε*(1+A)^K.card:= le_mul_of_one_le_right he.le (one_le_pow₀ (by linarith))
          have hg(j): ‖z 0 (w j)‖ ≤ ε*(1+A)^K.card:=by
             rw [hz]; refine ih (fun i hi=>hK i (Finset.mem_insert_of_mem hi)) (polar i x a (w j)) ?_ ?_ ?_
             · (unfold polar); exact (Function.update_of_ne (Ne.symm (hK i (Finset.mem_insert_self ..))) ..).trans h0
             · intro s; specialize hx s
               rw [Finset.card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one] at hx
               have hV:=norm_shift (radius_pos _ _|>.le) (x i.1) a ha (hw.1 j) (j:=i.2)
               unfold polar; by_cases ht:s=i.1
               · subst s; rw [Function.update_self]; linarith only [hx, hf, hV, norm_sub_le_norm_sub_add_norm_sub (streak i.2 (x i.1) a (w j)) (x i.1) (y i.1)]
               rw [Function.update_of_ne ht]; linarith only [hx, tolerates_le n hr|>.1]
             intro u hu bad0
             by_cases he:u=i
             · subst u; constructor
               · simpa [polar] using (hW j).1
               intro s hs; simpa [polar,Function.update_of_ne hs] using ((hW j).2 s)
             have hL := hb u (by simpa [hu,he] ) bad0
             have hP:polar i x a (w j) u.1 u.2=x u.1 u.2:=by
                 unfold polar; by_cases hs:u.1=i.1
                 · rw [hs,Function.update_self]; apply keep; rintro h; exact he (Prod.ext hs h)
                 simp [hs]
             refine ⟨hP.symm ▸ hL.1, fun s hs=>?_⟩; rw [hP]; by_cases hS:s=i.1
             · by_cases hU:u.2=i.2
               · rw [hS,polar,Function.update_self,hU]; exact Ne.symm (hW j|>.2 u.1)
               rw [hS,polar,Function.update_self,keep hU _ _]; exact hS ▸ hL.2 s hs
             rw [polar,Function.update_of_ne hS]; exact hL.2 _ hs
          have he': 0 ∈ Icc (-radius n D) (radius n D):=⟨by have ht:=radius_pos n D;linarith,(radius_pos n D).le⟩
          simpa only [Finset.card_insert_of_notMem hi,pow_succ,← mul_assoc, hz,Function.comp_apply,polar_zero] using ((H z _ w (he.trans_le hε) hw hg h₁ (fun t hh=>(h₂ t hh).trans hε) 0 he').trans (mul_le_mul_of_nonneg_left (by linarith) (he.trans_le hε).le))
    let K:=Finset.univ.filter (fun (i:Fin n×Axis)=>i.1≠default)
    have hk:K.card≤Fintype.card (Fin n×Axis):= Finset.card_le_univ _
    refine (ht K (fun i hi=> Finset.mem_filter.mp hi|>.2) y hy.1 (fun i=>?_ ) (fun i h hz=> (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩)).elim)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) hk) he.le)
    rw [sub_self,norm_zero,zero_add]; unfold p' tolerates
    have hh:(K.card:ℝ)≤4*n:=by exact_mod_cast (show K.card ≤4*n from (by simpa [Axis,Nat.mul_comm] using hk))
    field_simp; push_cast
    nlinarith only [hh,Nat.cast_nonneg (α:=ℝ) n]
end YM.MultipleContact.Bunching.Cord
