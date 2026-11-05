import YM.RG08.Ducat.School
/-! # Lift reclosure and separated strict stencil. Geometry equality out of finite precision -/
noncomputable section
namespace YM.RG08.Ducat
open Filter Function Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior
open scoped Classical BigOperators PowerSeries Topology
set_option autoImplicit false
variable {G:Gauge}{O:Type}{n m k e r:ℕ}{K:RG.KernelChoices}{P:RG.Patch}{B:Bed}{I J:Type}

lemma crosses(o:I↪J)(F:Flake n (Market I))(m:Kernel J (Loc G 1)) : Forms.raft (repeatLine m n) (Cairn.install o F)=raft (repeatLine (fun i j=>m (i.1,o i.2) j) n) F:=by
 ext x;rw [Forms.raft,← (Cairn.many (Cairn.hide o) n).injective.tsum_eq ?_];swap
 · intro y hy; by_contra! he
   change Forms.vat _ _ _ _≠0 at hy; rw [Forms.vat,Cairn.install_out _ _ he,zero_mul] at hy;exact hy rfl
 unfold Forms.raft; apply tsum_congr; intro i;unfold Forms.vat;rw [Cairn.install_in]; rfl

lemma surf (F: Flake n (Market (Loc G 1))) : Forms.raft (repeatLine (Prism.rains P K B) _) (Cairn.box _ F) = braces (Cell.plotted P K G B) F:=by
 unfold Cairn.box;rw [crosses, ← braces_farm (L:=P.L)]
 apply congrArg₂ (fun m F=>Forms.raft (repeatLine m n) F) _ rfl
 funext i j;unfold Prism.rains Cell.plotted Cell.out
 change (Cell.predictor P K G B) i j+0=(Cell.predictor P K G B) ((Cell.column P.L _).symm ((Cell.column P.L _) i)) j;rw [add_zero,Equiv.symm_apply_apply]

def Duo (G:Gauge)(P:Patch)(K:RG.KernelChoices)(B:Bed)(M:Kernel (TypeFace 2) (TypeFace 2)):=
 ∀ (r:ℕ)(F:Gird G r)(w c:ℝ), 0<w → 0≤c→ Cohort F→Forms.Sym F → Held (carpet _) w c F →
 Anchor.extend 1 (braces (Cell.plotted P K G B) (compress 1 (picture G.ColorIndex (RG08.Mount.rank r) F)))=voucher M F

-- `hσ, aperture comparison` variable depends on F: to inherit equality, can shrink θ & ask any v>0 coarsely. For every r unmarked.
variable {a:Levels G}{H:Horizon a}{X:MapPrices}
include H
omit H in
private lemma shoe {r:ℕ}(M:Kernel (TypeFace 2) (TypeFace 2))(F:Gird G r): Anchor.extend 1 (compress 1 (voucher M F))=voucher M F:=by
 let W:=pushField M F
 have he:Graded (voucher M F) (fun _=>1):=by -- general grade picture
    apply Symmetry.graded_iff.mpr;intro j
    have ht(k:ℕ)(l:List (Fin k))(h:l.Nodup)(F:Rudder.Raw G.ColorIndex k)(i:Fin k): Symmetry.field F i 2→Symmetry.field (patchL l F) i (if i∈l then 1 else 2):=by
       induction l generalizing F with
       | nil=>simp only [List.not_mem_nil, ↓reduceIte];apply id
       | cons j l ih=>
         intro hx;obtain ⟨hh,hM⟩:=List.nodup_cons.mp h
         by_cases he:i=j
         · subst i; have hy: Symmetry.field (boundary j F) j 1:=Symmetry.enters hx
           have hA :∀ (l:List (Fin k)), j∉l→ ∀ (T:Rudder.Raw G.ColorIndex k),Symmetry.field T j 1→Symmetry.field (patchL l T) j 1:=by
              intro l;induction l with
              | nil=> intro _ T h; exact h
              | cons i l ih=>
                intro hl T h; simp only [List.mem_cons,not_or] at hl
                exact ih hl.2 _ (Symmetry.passive h hl.1)
           rw [if_pos (List.mem_cons_self ..)];exact hA l hh _ hy
         have hy:=ih hM (boundary j F) (Symmetry.passive hx he); change Symmetry.field (patchL l (boundary j F)) i _;simpa [he] using! hy
    simpa [voucher,Rudder.picture,W] using! ht _ (List.finRange _) (List.nodup_finRange _) W j (Symmetry.graded_iff.mp Anchor.expand_grade j)
 apply Cast.compress_inj (k:=1) _ _ Anchor.expand_grade he
 ext i;exact Anchor.extend_top ..

theorem chorus (h:H.Suffices X)(i N:ℕ)(he:i<N){v D:ℝ}(hv:0<v)(h1:v ≤ 1)(hP:Cell.Warm G a.clock.kernel ((a.clock.op i 0).patch) (H.H N (i+1)) v D): Duo G ((a.clock.op i 0).patch) a.clock.kernel (H.H N (i+1)) (fine_share H N i):=by
 intro r F w c hw hc hz hK hF
 let s:ℝ:=min 1 (min (X.α (a.clock.J (i+1))) (X.α (a.clock.J i)))
 have hs:0<s:=lt_min zero_lt_one (lt_min (X.alpha_pos _) (X.alpha_pos _))
 let t:=min v (min s ((a.S.block i).val * (w/2)))
 have ht0:0<(a.S.block i).val*(w/2):= by have hh:0<(a.S.block i).val:=(a.S.block i).pos;exact mul_pos (Nat.cast_pos.mpr hh) (half_pos hw)
 have ht:0<t:=lt_min hv (lt_min hs ht0)
 rw [inherited h i N he (RG08.Mount.rank r) (stick r) v t w c D hv h1 ht hw hc F hz hK hF (min_le_left ..) ((min_le_right ..).trans (min_le_left ..)) ((min_le_right ..).trans (min_le_right ..)) hP, shoe]
end YM.RG08.Ducat
