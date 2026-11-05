import YM.UVExtension.Free.Theater
import YM.UVExtension.Free.Stack

/-! Choose consistent positive financial lift in the same parameter order. Retain precisely WHICH
part of the core is determined; only a Peak retarget still needed. -/
noncomputable section
namespace YM.UVExtension.Free
set_option autoImplicit false
open Filter Function Lattice RG Wilson Tree Precision Exterior Bloch Craft Next.Free Bid
open Matrix
open scoped Topology BigOperators Classical
variable {G : Gauge} {A : Levels G} {B H : Horizon A} {X Y : MapPrices} {l : ℕ → ℝ}

private def tender (A : Levels G) (l : ℕ → ℝ) (N i : ℕ) : C3 := Flight.rollFunds A.clock.kernel.penalty (l (A.clock.J (i+1))) (l (A.clock.J i)) (destination A N i)

/-- Need all n to identify the output (not single R). -/
private structure Record (B H : Horizon A) (l : ℕ→ℝ) where
    root : ℕ → ℕ → C3
    width i : ∃ x C : ℝ,0<x ∧ ∀ N,i<N→ (root N i).strip x C
    stamp N i (h:i<N) : SqActs (tender A l N i) (root N i)
    pos i n c : i < n → ((root n i).acts c).PosSemidef
    pins N i : i < N → ∀ (c f : Side) (h:f.val=c.val*(A.S.block i).val), Replaces ⟨A.S.block i,h⟩ (B.H N (i+1)) (B.H N i) (A.params (i+1)).clip (A.params i).clip A.clock.kernel.penalty (root N i) (B.towers N i) (H.towers N i)

private theorem decide_kernel (P : Supply.Sheet G) (Q : MapPrices) (l : ℕ→ℝ) {γ : ℕ→ℝ} {b : ℕ → ℕ}
    (hT : Catalog P.kernel Q l γ b):
    ∃ K : MapPrices, ∀ A : Levels G,A.clock.stage=P.profile → A.clock.kernel=P.kernel → Credit A γ b →
      ∀ B : Horizon A, Rack A Q B → Present A B l → ∃ T : Horizon A, Retained T B ∧ T.Suffices K ∧ Nonempty (Record B T l) := by
  choose y X z hy hz H' using fun i : ℕ => Work.F07.answer (TypeFace 3) (Q.Ω i) (Q.η i) (Q.α i) (Q.eta_pos i) (Q.alpha_pos i)
  choose t u ht I using fun i j : ℕ => Work.F08.answer (P.profile j).clip (P.profile i).clip P.kernel.penalty (Q.Ω j) (Q.α j) (Q.α i)
    (Q.Ω i) (z j) (X j) (j-2) P.kernel.penalty_pos (Q.alpha_pos j) (Q.alpha_pos i) (hz j)
  let K : MapPrices := { Q with
    α := fun j => min (Q.α j) (min (t j j) (t (j-1) j))
    Ω := fun j => max (Q.Ω j) (max (u j j) (u (j-1) j))
    alpha_pos := fun j => lt_min (Q.alpha_pos j) (lt_min (ht j j) (ht _ _)) }
  refine ⟨K,fun A he hb hv B R hP => ?_⟩
  have hm (N i : ℕ) : ∃ (T : Towers (A.S.block i)) (p:C3), i < N →
      let S := B.towers N i; let j := A.clock.J (i+1); let W := B.H N (i+1); let Y := B.H N i
      p.strip (z j) (X j) ∧ (∀ c, (p.acts c).PosSemidef) ∧ SqActs (tender A l N i) p ∧
        (∀ (c f : Side) (h:f.val=c.val*(A.S.block i).val), Replaces ⟨_,h⟩ W Y (A.params (i+1)).clip (A.params i).clip A.clock.kernel.penalty p S T) ∧
          T.Deep (K.α j) (K.Ω j) (j-2) ∧ T.A0=S.A0 ∧ T.T=S.T ∧ ∀ m : ℕ,
            Towers.Diagonal (A.clock.op i m) W Y T ∧ Towers.Roll (A.clock.op i m) W Y T (A.params (i+1)).clip (A.params i).clip := by
    by_cases Hn : i<N
    · let j := A.clock.J (i+1)
      let k := A.clock.J i
      have hk : k=j ∨ k=j-1 := by
        have hx : k ≤ j := A.fits.mono (Nat.le_succ i)
        have hh : j ≤ k+1 := A.fits.stepSlow i
        omega
      have hJ : Mag j k:= ⟨A.clock.adm _,A.clock.adm _,by
        have hp : k ≤ j:= A.fits.mono (Nat.le_succ i)
        have ht:j≤k+1:=A.fits.stepSlow i
        omega⟩
      have hs : (A.params i).clip = (P.profile k).clip := by unfold Levels.params Calendar.params; rw [he]
      have ha : (A.params (i+1)).clip = (P.profile j).clip := by unfold Levels.params Calendar.params; rw [he]
      let M:= tender A l N i
      let hw := destination A N i
      obtain ⟨-,h1,g2⟩:= hT.hop j k hJ hw
      unfold tender; rw [← hb] at h1 g2
      obtain ⟨M',hn,hM',hSq⟩ := H' j M h1 (g2 (hv.2 i))
      let L := A.S.block i
      obtain ⟨T,hF,h⟩ := I k j (B.H N (i+1)) (B.H N i) (R.covers _ _ Hn) (R.covers _ _ Hn.le)
        _ hM' L (A.S.block_odd i) _ (R.legs N i Hn)
      have hhP (c f : Side) (hz:f.val=c.val*L.val) : Replaces ⟨L,hz⟩ (B.H N (i+1)) (B.H N i) (A.params (i+1)).clip (A.params i).clip
          A.clock.kernel.penalty M' (B.towers N i) T := by rw [hs,ha,hb]; exact h c f hz
      refine ⟨T,M',fun _ => ?_⟩
      have hh (p : ℕ) : Replaces (A.clock.op i p).ratio (B.H N (i+1)) (B.H N i) (A.params (i+1)).clip (A.params i).clip
          (A.clock.op i p).kernel.penalty M' (B.towers N i) T := hhP _ _ (A.clock.op i p).sizes
      refine ⟨hM',fun i=> positive_root (hy j).le hn ⟨_,_,hz j,hM'⟩ i,hSq,hhP,
        ?_, (hh 0).first.symm, (hh 0).form.symm, fun p => ⟨?_, Work.F09.answer _ _ _ _ _ _ _ M' M _ _ _ _ _ _ (hh p) (R.traces _ _ Hn _) (R.traces _ _ Hn.le _) (R.crosses _ _ _ Hn) (fun n => (hSq n).1) ?_⟩⟩
      · have hα : K.α j ≤ t k j := le_trans (min_le_right ..) (hk.elim (fun he => by rw [he]; exact min_le_left ..) (fun he => by rw [he]; exact min_le_right ..))
        have hΩ : u k j ≤ K.Ω j := le_max_of_le_right (hk.elim (fun he => by rw [he]; exact le_max_left ..) (fun he => by rw [he]; exact le_max_right ..))
        obtain ⟨u1,u2,u3,u4⟩ := hF
        exact ⟨fun i j => (u1 i j).mono hα hΩ, fun i j => (u2 i j).mono hα hΩ,fun i j => (u3 i j).mono hα (div_le_div_of_nonneg_right hΩ (by positivity)),fun a hh => ⟨fun i j => ((u4 a hh).1 i j).mono hα (div_le_div_of_nonneg_right hΩ (by positivity)),fun i j => ((u4 a hh).2 i j).mono hα (div_le_div_of_nonneg_right hΩ (by positivity))⟩⟩
      · obtain ⟨hA,h2,h3⟩ := R.crosses N i p Hn
        constructor
        · rw [show T.A0=_ from (hh p).first.symm]; exact hA
        · rw [show T.T=_ from (hh p).form.symm]; exact h2
        rw [show T.A0=_ from (hh p).first.symm, show T.T=_ from (hh p).form.symm]; exact h3
      have hu:= hP.1 N (i+1) Hn; have hw':=hP.1 N i Hn.le
      rw [loc_land A N i Hn] at hw'
      have hx:=check_bleep A.clock.kernel (l k) (l j) (hT.net _) (hT.net _) (A.clock.adm i) (P:=hw) (B.H N (i+1)) (B.H N i) hu hw' (c:=A.S.side i p) (f:=A.S.side (i+1) p) (A.clock.op i p).sizes
      unfold Bleeps defect at *
      -- A0 unnecessary. actual common T from Present
      erw [(hP.2 N i Hn).2]; exact hx
    exact ⟨B.towers N i,0,fun H => False.elim (Hn H)⟩
  choose t p hM using hm
  let T := { B with towers := t }
  have hT (N i) (h:i<N):= (hM N i h).2.2.2.2
  refine ⟨T,⟨rfl,fun N i ha => ⟨(hT _ _ ha).2.1,(hT _ _ ha).2.2.1⟩⟩,?_,⟨⟨p,fun i=> ⟨_,_, hz (A.clock.J (i+1)),fun N hn=> (hM _ _ hn).1⟩,fun N i h=> (hM _ _ h).2.2.1,fun i n c h=> (hM n i h).2.1 c,fun N i h=> (hM _ _ h).2.2.2.1⟩⟩⟩
  refine ⟨fun N i hi => ?_, fun N i hi n => ?_,fun N i hi => (hT N i hi).1,fun N i p hi => ((hT N i hi).2.2.2 p).1,
    fun N i p hi => ((hT N i hi).2.2.2 p).2, R.top⟩
  · exact cover_revise (R.covers _ _ hi) (min_le_left ..) (le_max_left ..)
  exact floor_revise (R.traces _ _ hi _) le_rfl (le_max_left ..)

/-- Structural UV receipt; covers data even inside deterministic masks and tower projections. -/
structure Report (H : Horizon A) (X : MapPrices) : Prop where
  bed i : ∃ W, MetricReport (fun n=> H.H n i) W (X.α (A.clock.J i)) (X.Ω (A.clock.J i))
  columns i : let a := X.α (A.clock.J (i+1))
              let b := X.Ω (A.clock.J (i+1))
              let L : ℝ := (A.S.block i).val
              let T := fun n=> H.towers n i
              ∃ P : Towers (A.S.block i),
                  Received (fun n=> (T n).A0) P.A0 a (b / L^1) ∧
                  Received (fun n=> (T n).T) P.T a (b / L^2) ∧
                  Received (fun n=> (T n).mf) P.mf a (b / L^2) ∧
                  Received (fun n=> (T n).mn) P.mn a b ∧
                  Received (fun n=> (T n).o) P.o a b

lemma ledger {V : ℕ → Bed} (h : ∀ p, Arrives fun n=> ((V n).roots.acts p)) (p : Clip) (n : Side) :
    Arrives fun i=> (V i).full p n := by
  obtain ⟨z,ht⟩ := h n
  apply Arrives.columns; intro i; apply Arrives.columns; intro j
  unfold Bed.full; obtain ⟨q,x|x⟩:=i
  · exact Arrives.steady _
  exact ⟨_,tendsto_pi_nhds.mp (tendsto_pi_nhds.mp ht _) _⟩

private lemma reporting {A : Levels G} {Z : MapPrices} (B H : Horizon A) (R : Record B H l) (h : Rack A Y B)
    (he : H.Suffices Z) (hp : Present A B l) (hl : ∀ k, 0 ≤ l k)
    (hv : Retained H B) (hs : SmoothMetric A B): Report H Z:= by
  have ht i:= receives_metric B Y _ i hl h hp hs
  let a i:= A.clock.J i
  let M i:= Z.α (a i); let b i:=Z.Ω (a i)
  let k:= A.clock.kernel.penalty; have hk : 0<k:= A.clock.kernel.penalty_pos
  have hB i: ∃ (W:Bed), MetricReport (fun n=> B.H n i) W (M i) (b i):= by
    obtain ⟨W,hW⟩:= ht i
    have he:∀ᶠ n in atTop,(B.H n i).covered (M i) (b i):= (eventually_ge_atTop _).mono fun N hi=> by
      rw [← hv.1]; exact he.rows N i hi
    exact ⟨W,reported hW.diag.entries (he.mono fun i h=> h.1),reported hW.dual.entries (he.mono fun i h=> h.2.2.2.2),reported hW.metric.entries (he.mono fun i h=> h.2.1),reported hW.inverse.entries (he.mono fun i h=> h.2.2.1),reported hW.roots.entries (he.mono fun i h=> h.2.2.2.1)⟩
  have hH i:∀ᶠ n in atTop,(B.H n i).covered (M i) (b i):= (eventually_ge_atTop _).mono fun N hi=> by
      rw [← hv.1]; exact he.rows N i hi
  refine ⟨by rw [hv.1]; exact hB,fun i=>?_⟩
  let j:= A.clock.J (i+1); let t n:= H.towers n i; let p:=A.params i; let S:=A.params (i+1); let L:= A.S.block i
  let D n:=B.H n i; let D' n:= B.H n (i+1)
  have hF:∀ᶠ n in atTop,(t n).Deep (M (i+1)) (b (i+1)) (j-2):= (eventually_gt_atTop _).mono fun N hi=> he.costs N i hi
  obtain ⟨h₁,h₂,-⟩:= tower_fields A i k hk
  have hT : ∀ᶠ n in atTop, ((t n).A0=(Flight.duo k (destination A n i)).A0 ∧ (t n).T=(Flight.duo k (destination A n i)).T):=
      (eventually_gt_atTop _).mono fun n hn=> by obtain ⟨ha,hT⟩:= hv.2 n i hn; exact ⟨ha.trans (hp.2 n i hn).1,hT.trans (hp.2 n i hn).2⟩
  have hx : 0<M (i+1):= Z.alpha_pos _
  obtain ⟨V,hV⟩:= Sailing.has h₁ hx (y:= b (i+1)/(L.val:ℝ)^1) ((hF.and hT).mono fun n hh=> by
    have ht:=(hh.1.2.2.2 [] (Nat.zero_le _)).1; change (t n).A0.strip _ _ at ht; rw [hh.2.1] at ht; exact ht)
  obtain ⟨T,hQ⟩:= Sailing.has h₂ hx (y:= b (i+1)/(L.val:ℝ)^2) ((hF.and hT).mono fun n hh=> by
    have ht:=(hh.1.2.2.2 [] (Nat.zero_le _)).2; change (t n).T.strip _ _ at ht; rw [hh.2.2] at ht; exact ht)
  have hQ' : Sailing (tender A l · i):= reel A i k hk (l _) (l _) (hl _)
  obtain ⟨s,X,hX,Hw⟩:= R.width i
  have ht' : ∀ᶠ n in atTop, (R.root n i).strip s X∧ ∀ c, ((R.root n i).acts c).PosSemidef := (eventually_gt_atTop _).mono fun n hn=> ⟨Hw n hn,fun c=> R.pos i n c hn⟩
  obtain ⟨U,hU⟩:= square_limit (A:=fun n=> R.root n i) hX ht' (fun n=> (hQ'.2 n).copy
    ((eventually_gt_atTop _).mono fun j h=> (R.stamp j i h n).1))
  have hθ := hF.mono fun n hn=> hn.2.2.1
  have hr (c f:Side)(p:f.val=c.val*L.val):= (eventually_gt_atTop i).mono (fun n h=> R.pins n i h c f p)
  have hI i c : Arrives fun n=> (B.H n i).inverse.acts c:= by
    obtain ⟨w,h⟩:= hB i; exact ⟨_,acts_limit h.inverse ((hH i).mono fun n H=> H.2.2.1) (Z.alpha_pos _) _⟩
  have hz i c : Arrives fun n=> (B.H n i).full (A.params i).clip c := by
    apply ledger (V:=fun n=> B.H n i); intro t
    obtain ⟨w,h⟩:= hB i; exact ⟨_,acts_limit h.roots ((hH i).mono fun n H=> H.2.2.2.1) (Z.alpha_pos _) _⟩
  obtain ⟨f,hf⟩:= acts_suffice (T:=fun n=>(t n).mf) hx hθ (from_installations (V:=fun n=> (t n).mf) (fun c f h=>by
    have hA : Arrives fun n=> installed ⟨L,(show f.val=c.val*L.val from h)⟩ (B.towers n i).T := (installations h₂ c f h).copy
      ((eventually_gt_atTop _).mono fun n hn=> (congr_arg (fun A:Cross L (TypeFace 2) (TypeFace 2)=> installed ⟨_,(show f.val=c.val*L.val from h)⟩ A) (hp.2 n i hn).2.symm))
    exact (matR (matR (matR (hz (i+1) f) (hI (i+1) f)) hA) ((hz i c).post (T:=Matrix.transpose) (by fun_prop))).copy
      ((hr c f h).mono fun n h=> h.mf.symm)))
  obtain ⟨y,hY⟩:= acts_suffice (T:=fun n=>(t n).mn) hx (hF.mono fun n h=> h.1) (fun c=>
    ((hz i c).post (T:=fun x:Matrix _ _ ℝ=> (Real.sqrt k)⁻¹ • ((d 1 c)ᵀ*xᵀ)) (by fun_prop)).copy
      ((hr c (c*L) rfl).mono fun n h=> h.mn.symm))
  obtain ⟨z,hZ⟩:= acts_suffice (T:=fun n=>(t n).o) hx (hF.mono fun n h=>h.2.1) (fun c=> by
    let v:= d 2 c; let b n:= (R.root n i).acts c
    have hv : Arrives b:= ⟨_,acts_limit hU (ht'.mono fun n h=> h.1) hX c⟩
    have hx : Continuous fun p : (Matrix (Body 2 c) (Body 2 c) ℝ× Matrix (Co c Layers2) (Body 2 c) ℝ) × Matrix (Body 3 c) (Body 3 c) ℝ=> stack (1-p.1.2*p.1.1*p.1.2ᵀ) (p.2*v*p.1.1*p.1.2ᵀ) := by
      apply continuous_matrix; intro i' j; rcases i' with ⟨x,y|y⟩ <;> unfold stack <;> simp only [Matrix.of_apply,Sum.elim] <;> fun_prop
    exact ((((hI i c).pair (hz i c)).pair hv).post hx).copy ((hr c (c*L) rfl).mono fun n hh=> hh.image.symm))
  exact ⟨⟨V,T,f,y,z⟩,retake hV (hT.mono fun n h=>h.1.symm),retake hQ (hT.mono fun n h=>h.2.symm), hf,hY,hZ⟩

lemma profiles (k : KernelChoices):
    ∃ (X : MapPrices) (l γ : ℕ→ℝ) (b:ℕ→ℕ), Catalog k X l γ b ∧ ∀ P : Supply.Sheet G, P.kernel=k →
      ∃ Y : MapPrices, ∀ A:Levels G,A.clock.stage=P.profile→A.clock.kernel=k→ Credit A γ b → ∃ U V:Horizon A,
        Rack A X U ∧ Present A U l ∧ Retained V U ∧ V.Suffices Y ∧ Present A V l ∧ (∀ N m n,m≤N → Sworn (V.H N m) n G) ∧ Report V Y:=by
  obtain ⟨X,l,γ,b,hK,h⟩:= strong_pledges k
  refine ⟨X,l,γ,b,hK,fun P hp=>?_⟩
  obtain ⟨Q,hQ⟩:= decide_kernel P X l (γ:=γ) (b:=b) (hp.symm ▸ hK)
  refine ⟨Q,fun A hS hT hu=>?_⟩
  obtain ⟨M,hM,hR,H⟩:= strengthened_shelves A X l γ b (hT.symm ▸ hK) (hT.symm ▸ h) hu
  obtain ⟨T,hf,ht,⟨u⟩⟩:= hQ A hS (hT.trans hp.symm) hu M hM H
  have hx:=retained_presents A X M T H hM hf
  exact ⟨M,T,hM,H,hf,ht,hx.1,hx.2,reporting M T u hM ht H hK.net hf hR⟩
end YM.UVExtension.Free
