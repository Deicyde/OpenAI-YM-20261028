import YM.RG12.Shadows.Mantle
/-! First derivative invisible under joint signs for a covariance discrepancy.
Need exact Through on UNDERLYING gauge at literal V1 at least twice. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Shadows
open Set Metric Filter Function ConnectedActivityE6 ConnectedActivityE6.Blaze
open scoped ContDiff Topology BigOperators Classical
variable {R:Haze}{p q:ℝ}{I E F:ℕ→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)][∀ i,NormedAddCommGroup (F i)][∀ i,NormedSpace ℝ (F i)]
structure Sleeve (R:Haze)(p q t:ℝ)(f:Counter I E F):Prop where
   smooth:Smooths 2 f
   zero:Flares R 0 p f
   first:Flares R 1 q f
   second:Flares R 2 t f
namespace Sleeve
variable {v t w:ℝ}{f g h k: Counter I E F} (H:Sleeve R p q t f){n:ℕ}
include H
lemma flares (i:ℕ)(hi:i≤2)(hp:v≤p)(hq:v≤q)(ht:v≤t): Flares R i v f:=by interval_cases i; exacts [H.zero.mono hp,H.first.mono hq,H.second.mono ht]
-- pack brush shared fee.Disjoint θ.
lemma brush (hp:v≤p)(hq:v≤q)(ht:v≤t): ∃ w,Charges R v w ∧ ∀ᶠ i:ℕ in atTop,∀ j,Brush 2 (w i) 1 (f i j) 0:=by
   obtain ⟨A,hA,HA'⟩:= (H.zero.mono hp).assumes; obtain ⟨B,hB,HB'⟩:=(H.first.mono hq).assumes; obtain ⟨C,hC,HC'⟩:=(H.second.mono ht).assumes
   refine ⟨_,(hA.add hB).add hC,?_⟩
   filter_upwards [H.smooth,HA',HB',HC'] with i hs hA hB hC j
   refine ⟨hs j,zero_le_one,fun n hn=>?_⟩; rw [one_pow, mul_one]
   have hA':= (norm_nonneg _).trans (hA j); have hB':=(norm_nonneg _).trans (hB j); have hC':=(norm_nonneg _).trans (hC j); interval_cases n
   · linarith only [hA j,hB',hC']
   · linarith only [hB j,hA',hC']
   linarith only [hC j,hA',hB']
omit H in
lemma call {f:Drift I E}(H:Sleeve R p q t f)(hp:v≤p)(hq:v≤q)(ht:v≤t):Call R 2 v f:= H.brush hp hq ht
lemma flips : Sleeve R p q t (fun i j y=>f i j (-y)):=
  ⟨Eventually.mono H.smooth fun i hi j=> (show ContDiffAt ℝ _ (f i j) (-0) from by rw [neg_zero]; exact hi j).comp (f:=fun y:E i=> -y) _ contDiff_neg.contDiffAt,H.zero.flip (H.smooth.mono (by decide)),H.first.flip (H.smooth.mono (by decide)),H.second.flip H.smooth⟩
lemma grids {I':ℕ→Type} (r:∀i,I' i→ I i): Sleeve R p q t (fun i k=>f i (r i k)) :=
  ⟨Eventually.mono H.smooth fun _ hi _=>hi _,Keeps.rename H.zero r, Keeps.rename H.first r,Keeps.rename H.second r⟩
lemma mono {z:ℝ}(hr:v≤p)(hs:w≤q)(hz:z ≤ t): Sleeve R v w z f:=
   ⟨H.smooth,H.zero.mono hr,H.first.mono hs,H.second.mono hz⟩
lemma scales {B:ℕ→ℝ}(hB:Charges R v B): Sleeve R (p+v) (q+v) (t+v) (fun i=>B i • f i):=
  ⟨Eventually.mono H.smooth fun _ hi j=>(hi j).const_smul _,H.zero.scales hB (H.smooth.mono (by decide)),H.first.scales hB (H.smooth.mono (by decide)),H.second.scales hB H.smooth⟩
lemma sub (hk:Sleeve R p q t g):Sleeve R p q t (f-g):=
  ⟨(Filter.Eventually.and H.smooth hk.smooth).mono fun _ hi j=>(hi.1 j).sub (hi.2 j),H.zero.subs hk.zero (H.smooth.mono (by decide)) (hk.smooth.mono (by decide)),H.first.subs hk.first (H.smooth.mono (by decide)) (hk.smooth.mono (by decide)),H.second.subs hk.second H.smooth hk.smooth⟩
lemma congr (hf:∀ᶠ i:ℕ in atTop,∀ j,g i j =ᶠ[𝓝 0] f i j) : Sleeve R p q t g:=⟨(Filter.Eventually.and H.smooth hf).mono fun _ hi j=> (hi.1 j).congr_of_eventuallyEq (hi.2 j),H.zero.sameZero hf,H.first.sameZero hf,H.second.sameZero hf⟩
end Sleeve
section
variable {f g:Drift I E}(H:Sleeve R p (p+1) (p+1) f)
include H
lemma test :Touch R 2 p true f (fun i j y=> f i j (-y)):=by
   let B(i:ℕ) j y:=f i j (-y); have hf:=H.flips; have ht := H.smooth; have hb:=hf.smooth
   let h:= f-B; have hh := (H.sub hf)
   have he : Sleeve R (p+1) (p+1) (p+1) h:= ⟨hh.smooth, Flares.mk (Charges.idle (p+1) R) (Eventually.of_forall (fun i j=> by simp [normJ,B,h])), hh.first,hh.second⟩
   refine ⟨H.call le_rfl (by linarith) (by linarith),?_⟩
   simpa only [aura,one_smul] using! he.call le_rfl le_rfl le_rfl
omit H in
lemma alt {p} (H:Sleeve R (p+1) p (p+1) f) :Touch R 2 p false f (fun i j y=>f i j (-y)):=by
   let g(i:ℕ) j y:=-f i j (-y); have hs:= H.flips; let h:=f-g
   have hg:Sleeve R (p+1) p (p+1) g:=by
     simpa only [add_zero,neg_one_smul] using! hs.scales (Charges.frozen (-1) R)
   have he:=H.sub hg
   have hf : Sleeve R (p+1) (p+1) (p+1) h:= by
      refine ⟨he.smooth,he.zero,Flares.mk (Charges.idle _ R) ?_,he.second⟩
      filter_upwards [H.smooth.mono (m:=1) (by decide),hg.smooth.mono (m:=1) (by decide)] with i hv hk j
      change normJ 1 (f i j-g i j) (0:E i)≤0
      let W (y:E i):= f i j (-y)
      have hw:ContDiffAt ℝ (↑(1:ℕ)) W 0:= (show ContDiffAt ℝ _ (f i j) (-0) from by rw [neg_zero]; exact hv j).comp (f:=(-·:E i→ E i)) _ contDiff_neg.contDiffAt
      rw [show g i j = (-1:ℝ) • W from by rw [neg_one_smul]; rfl,normJ]
      rw [iteratedFDeriv_sub_apply (hv j) (show ContDiffAt ℝ (↑(1:ℕ)) ((-1:ℝ) • W) (0:E i) from hw.const_smul (-1:ℝ)),iteratedFDeriv_const_smul_apply hw, show W=(fun x=> f i j (-x)) from rfl,iter_neg _ (hv j)]
      simp
   refine ⟨H.call (by linarith) le_rfl (by linarith),?_⟩
   exact (hf.call le_rfl le_rfl le_rfl).same (fun i j x=> by unfold h g; simp [aura])
lemma ledge (G:Sleeve R (p+2) (p+1) (p+2) (g-f)):Tilts R 2 p true f (fun i j y=> f i j (-y)) g (fun i j y=>g i j (-y)):=by
  refine ⟨test H,?_⟩
  rw [show Bool.not true = false from rfl]
  change Touch R 2 (p+1) false (g-f) (fun i j y=>(g-f) i j (-y))
  exact alt (by simpa only [add_assoc,show (1:ℝ)+1=2 by norm_num] using! G)
end
end YM.RG12.Shadows
