import YM.MultipleContact.Multi.Plant
import YM.MergeProof.West.Sally
import YM.MergeProof.North.Cent
import YM.MergeProof.North.Brim
import YM.Extraction.Held
/-! Bringing finite physical configurations to common tilings on cofinal cutoff tails. -/
set_option autoImplicit false
set_option maxHeartbeats 2300000
noncomputable section
namespace YM.MultipleContact.Terrain
open Function Filter Set MeasureTheory Lattice Cells Extraction Extraction.Around MergeProof.Ribbons Wilson Arbor
open Gaps
open scoped Topology BigOperators Classical
variable {G:Gauge} {S:Schedule}{N p:ℕ}{n t:ℕ}
local notation "Λ" => S.side N p
private lemma toDepth_list (x:Fin n → Cover) (h:t≤N):
    tag (S.a N) (fun i=> (span S h p)• x i) = points (S.gridPoint t ∘ x):=by
      have ht:=S.embeds_scale (S.toDepth h p); ext i s
      change S.a N * (↑(((span S h p) • x i:Cover) s) :ℝ) = _
      simp only [Pi.smul_apply,nsmul_eq_mul]
      change S.a N * _=S.a t*(x i s:ℝ)
      push_cast
      rw [← ht]; dsimp only [Cells.span]; ring
private lemma pdist_physical (z:Cover)(h:t≤N):S.a N*pdist (location S t N p z) ≤ ‖S.gridPoint t z‖:=by
   let y:=Cells.span S h p • z
   rw [location,dif_pos h,Ratio.embed_wrap]
   change S.a N * (pdist (wrap (S.side N p) y) :ℝ) ≤ _
   have ht:= S.embeds_scale (S.toDepth h p); have hpos:= S.a_pos N
   let g(s:Axis):=(lift (wrap (S.side N p) y) s).natAbs
   obtain ⟨i,hi,hq⟩:=Finset.exists_mem_eq_sup' Finset.univ_nonempty g
   rw [Finset.sup'_eq_sup] at hq
   change _ = _ at hq
   unfold pdist
   rw [hq]; change S.a _ * (g i:ℝ) ≤ ‖_‖
   have he:g i ≤ ((Cells.span S h p) * (z i).natAbs):=by
       have he := Lattice.Corona.lap (n:=S.side N p) y i
       have he' : (y i).natAbs = (span S h p) * (z i).natAbs:=by change ((span S h p) • (z i:ℤ)).natAbs=_; simp only [nsmul_eq_mul]; exact Int.natAbs_mul (span S h p : ℤ) (z i) |>.trans (by simp)
       exact he.trans_eq he'
   calc _ ≤ S.a t*((z i).natAbs:ℕ):=by
             calc _ ≤ S.a N * (Cells.span S h p *(↑(z i).natAbs : ℝ)) := mul_le_mul_of_nonneg_left (by exact_mod_cast he) hpos.le
                  _ = _:= by rw [← ht]; dsimp only [span]; ring
        _ = |S.gridPoint t z i|:=by
             change _=|S.a _ * (z i:ℝ)|
             rw [abs_mul,abs_of_pos (S.a_pos _), show ((↑(z i).natAbs:ℕ):ℝ)=|(z i:ℝ)| from ((by rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]))]
        _ ≤ _:=by rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le ..
lemma wide {μ:ℕ}(x:Fin n → Cover)
   (hsep:∀i j:Fin n,i≠j → 4*S.a μ < ‖S.gridPoint t (x j)-S.gridPoint t (x i)‖):
   ∀ᶠ p in atTop,∀ N:ℕ, ∀ (hm:μ≤N)(_:t≤N), let y:=location S t N p ∘ x; ∀i j:Fin n,i≠j → Cells.span S hm p < separation (y i) (y j):=by
    let z:= points (S.gridPoint t ∘ x); have hh:=Gaps.expand_equivalent S (isCompact_singleton (x:=z))
    filter_upwards [hh] with p hp N hμ ht y i j hij
    obtain ⟨a,ha⟩:=above_coord (S.a μ) (S.gridPoint t (x j)-S.gridPoint t (x i)) (hsep i j hij)
    change _ < |distances z i j a| at ha
    have hD:=hp z (Set.mem_singleton z) i j a; let u(k:Fin n):= (span S ht p) • x k
    have hz:z=tag (S.a N) u:= (toDepth_list (p:=p) x ht).symm
    have hy(k):y k=wrap (S.side N p) (u k):=by dsimp only [y,u,Function.comp_apply,location]; rw [dif_pos ht,Ratio.embed_wrap]
    let w := lift (y j - y i) a
    have hw:wrap (S.side N p) (u j-u i) a = (↑w:Per (S.side N p)):=by
          change _= wrap (S.side N p) (lift (y j-y i)) a
          rw [map_sub,← hy,← hy,wrap_lift]
    have hT : |distances z i j a| ≤ S.a N * |(w:ℝ)|:= Gaps.torus S w hw (hz ▸ hD)
    have hh:= component_le (y j - y i) a
    change w.natAbs ≤ separation (y j) (y i) at hh
    rw [show |(w:ℝ)|=(w.natAbs:ℝ) from (by rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs])] at hT -- no separation in hT! remove
    have hw' := S.embeds_scale (S.toDepth hμ p)
    have hi':(w.natAbs:ℝ) ≤ ((separation (y i) (y j)):ℝ):= by
          exact_mod_cast hh.trans_eq (separation_comm ..)
    apply Nat.cast_lt (α:=ℝ) |>.mp
    exact lt_of_mul_lt_mul_left (show S.a N*(Cells.span S hμ p:ℝ)< _ from hw'.trans_lt (ha.trans_le (hT.trans (mul_le_mul_of_nonneg_left hi' (S.a_pos _).le)))) (S.a_pos _).le

lemma rendezvous {G:Gauge}(C:Family G)(hC:C.Makes)(k μ:ℕ)(hC0:μ ≤ k)(x:Fin n → Cover)
   (hR:(n:ℝ)*(6*C.S.a k) < C.S.a μ)
   (hs:∀i j:Fin n,i≠j → 4*C.S.a μ < ‖C.S.gridPoint t (x j)-C.S.gridPoint t (x i)‖):
   ∀ᶠ p:ℕ in atTop,∀ᶠ N:ℕ in atTop,∃ h:k≤N,∀ Gm:Fin n→ Config G (C.side N p)→ℂ,∀ A:Fin n→ℝ,(∀i,Interior ((center C.S p h 0).chamber 0) (Gm i) ∧ (center C.S p h 0).rootTest (C.beta N p) (Gm i)≤ A i) →
       ‖moment (C.beta N p) (fun U=>∏ i:Fin n, Gm i (translate (Cells.location C.S t N p (x i)) U))‖≤ ∏ i:Fin n,A i:=by
    filter_upwards [wide x hs] with p hp
    filter_upwards [eventually_ge_atTop k,(eventually_ge_atTop t:∀ᶠ j in atTop,t ≤ j)] with N hk hj
    let hm:=hC0.trans hk; let T:=center C.S p hm 0
    let hK':=C.S.embeds_scale (C.S.toDepth hk p); have he':=C.S.embeds_scale (C.S.toDepth hm p)
    have hK:n*(2*(3*Cells.span C.S hk p)) < T.side.val:=by
        apply Nat.cast_lt (α:=ℝ) |>.mp
        apply lt_of_mul_lt_mul_left _ (C.S.a_pos N).le
        change C.S.a N * _ < C.S.a N*(↑(span C.S hm p):ℝ); rw [he']; push_cast
        rw [← hK'] at hR; dsimp [span]; linarith
    refine ⟨hk,fun Gm A ha=>?_⟩
    exact Arbor.simultaneous (seamless hC N p) (T:=T) (fun _=>k) (fun _=>hk) (fun _=>inherits hC0 hk) A Gm ha _ (fun i=> (Cells.span C.S hj p) • x i) (fun i=>by rw [location,dif_pos hj,Ratio.embed_wrap]) (hp N hm hj) (by have := (C.S.toDepth hk p).count.pos; positivity) hK (fun _=>le_refl _)

lemma micro_actual {G:Gauge}(C:Family G)(hC:C.Makes)(k μ m:ℕ)(hC0:μ ≤ m)(hC':k≤ μ)(x:Fin n→ Cover)
   (hSmall:∀i,8*‖C.S.gridPoint t (x i)‖ ≤ C.S.a k)
   (hsep:∀i j:Fin n,i≠j → 4*C.S.a μ < ‖C.S.gridPoint t (x j)-C.S.gridPoint t (x i)‖)
   (hR:(Fintype.card (Signed×Fin n):ℝ)*(6*C.S.a m) < C.S.a μ)(hc: 2*C.S.a μ < C.S.a k)(d:Fin n→ℕ):
   ∀ᶠ p:ℕ in atTop,∀ᶠ N:ℕ in atTop,∃ h:k≤N,∃ hm:m≤N, let T:=center C.S p h 0;let T1:=center C.S p hm 0;let β:= C.beta N p;
    ∀ V:∀i,C.book.Ref (d i),∀ A:Fin n→ℝ,(∀i,Interior (T1.chamber 0) (C.O N p (d:=d i) (V i) 0) ∧ T1.rootTest β (C.O N p (d:=d i) (V i) 0)≤ A i) → let cfg(U:Config G (C.side N p)):= ∏ i:Fin n, C.O N p (d:=d i) (V i) (location C.S t N p (x i)) U; Interior (T.chamber 0) cfg ∧ T.rootTest β cfg ≤ ∏ i:Fin n,A i:=by
      filter_upwards [wide x hsep, eventually_all.mpr fun i=>faraway C t (x i)] with p hp hf
      filter_upwards [eventually_ge_atTop m,(eventually_ge_atTop t:∀ᶠ i:ℕ in atTop,t ≤ i),eventually_all.mpr fun v=>near_center C k (d v) hC] with N hm ht hq
      let U:=C.S; let hμ:=hC0.trans hm; let hk:=hC'.trans hμ
      refine ⟨hk,hm,?_⟩; let X:=center U p hμ 0 -- notation
      have hsN(j)(hj:j≤N):C.S.a N*span C.S hj p=C.S.a j:=C.S.embeds_scale (C.S.toDepth hj p)
      have hN:=C.S.a_pos N
      let g:= location C.S t N p ∘ x
      intro T T1 β V A hBudget cfg
      have hz(i):U.place (m:=N) (p:=p) (g i)=U.gridPoint t (x i):=by dsimp only [location,Function.comp,g,U]; rw [dif_pos ht,C.S.embeds_place,hf]
      have he(i):4*pdist (g i) ≤ T.side.val:=by
          apply Nat.cast_le (α:=ℝ) |>.mp; apply le_of_mul_le_mul_left _ hN
          push_cast
          change _ ≤ C.S.a N*(span U hk p)
          have h0:= pdist_physical (p:=p) (x i) (t:=t) (S:=C.S) ht; rw [hsN]; unfold g; dsimp only [Function.comp_apply]; linarith only [h0,norm_nonneg (U.gridPoint t (x i)),hSmall i]
      have h1: X.side.val ∣ T.side.val := Extraction.Around.inherits hC' hμ
      have h2: Cells.span U hm p ∣ X.side.val:=Extraction.Around.inherits hC0 hm
      have h3: Fintype.card (Signed×Fin n)*(2*(3*Cells.span U hm p)) < X.side.val:= by
          apply Nat.cast_lt (α:=ℝ) |>.mp; apply lt_of_mul_lt_mul_left _ hN.le
          push_cast; change _ < C.S.a N*(span U hμ p:ℝ)
          rw [← hsN _ hm, ← hsN _ hμ] at hR; unfold U; linarith only [hR]
      have h4: 2*X.side.val < T.side.val:=by
          apply Nat.cast_lt (α:=ℝ) |>.mp
          apply lt_of_mul_lt_mul_left _ hN.le
          push_cast
          change C.S.a N*(2*(span U hμ p:ℝ)) < C.S.a N*(span U hk p:ℝ)
          rw [← hsN _ hk,← hsN _ hμ] at hc; unfold U; linarith only [hc]
      have hcQ:= Arbor.micro hk (T:=X) (Y:=T) rfl hm h2 h1 h4 g he (hp N hμ ht) (seamless hC N p) h3 A (fun i=>C.O N p (d:=d i) (V i) 0) hBudget

      have hb' (l:Finset (Fin n)): Interior (T.chamber 0) (fun v=>l.prod fun i=> C.O N p (d:=d i) (V i) (g i) v):=by
          induction l using Finset.induction with
          | empty=> simpa using (Interior.constant (T.chamber 0) (1:ℂ) (G:=G))
          | insert i l hi ih=> simpa [Finset.prod_insert hi] using! Interior.times (hq i hk p (g i) (hz i ▸ hSmall i) (V i)) ih
      refine ⟨hb' _, hcQ.trans' ?_⟩
      exact le_of_eq (congrArg (T.rootTest β) (funext fun v=>Finset.prod_congr rfl fun i hi=>by rw [C.translation,zero_add];rfl))
end YM.MultipleContact.Terrain
