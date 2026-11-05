import YM.TraceExtension.Det.Ream
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Det
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}
variable {X Y Z:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y][NormedAddCommGroup Z][NormedSpace ℝ Z]
    {o:Site f}{F H:Acr G f→ X}{m n:ℕ}{α β C D A:ℝ}
variable (G f)
def af (z:pairA G f): Site f:= z.elim Prod.fst Prod.fst
abbrev aleft : Acr G f→L[ℝ] Link G f:= ContinuousLinearMap.fst _ _ _ ∘L (bite G f).toContinuousLinearMap
abbrev aright : Acr G f→L[ℝ] Link G f:=ContinuousLinearMap.snd _ _ _ ∘L (bite G f).toContinuousLinearMap
def takea: Link G f→L[ℝ] Acr G f := (bite G f).symm.toContinuousLinearMap ∘L ContinuousLinearMap.inl ..
abbrev splitp (U:Acr G f):=input G f (aright G f U)*input G f (aleft G f U)
abbrev bchip (U:Acr G f):= content (splitp G f U)
lemma bite_l (z:Lines G f 1): aleft G f (bolt (Sum.inl z))=bolt z:=by ext i;change bolt (ι:=pairA G f) (.inl z) (.inl i)= bolt _ _; simp[bolt,Pi.single_apply]
lemma bite_r (z:Lines G f 1): aright G f (bolt (Sum.inr z))=bolt z:=by ext i; change bolt (ι:=pairA G f) (.inr z) (.inr i)= bolt _ _; simp [bolt,Pi.single_apply]
lemma bite_lr (z:Lines G f 1): aleft G f (bolt (Sum.inr z))=0:=by ext i; change bolt (ι:=pairA G f) (.inr z) (.inl i)=0;simp [bolt]
lemma bite_rl (z:Lines G f 1): aright G f (bolt (Sum.inl z))=0:=by ext i; change bolt (ι:=pairA G f) (.inl z) (.inr i)=0;simp [bolt]
@[simp] lemma at_take (x): bite G f (takea G f x)=(x,0):=by unfold takea; simp
lemma al_take (x): aleft G f (takea G f x)=x:=show (bite G f (takea G f x)).1=x by simp
lemma ar_take (x): aright G f (takea G f x)=0:=show (bite G f (takea G f x)).2=0 by simp
lemma taken (x): takea G f (bolt x)=bolt (.inl x):= (bite G f).injective (by rw[at_take]; exact Prod.ext (bite_l G f x).symm (bite_rl G f x).symm)
lemma a_f (x:Site f)(i:pairA G f): landW x i=separation x (af G f i):=by cases i with
 | inl j=>rfl
 | inr j=>rfl
lemma pay_gate : Multiplicity (Prod.fst:Lines G f n→ Site f) (Fintype.card (Loc G n)):=by
    intro v; let s:= univ.filter fun i:Lines G f n=>i.1=v
    change s.card ≤ _; rw[← Finset.card_univ]; apply Finset.card_le_card_of_injOn (f:=fun i:Lines G f n=>i.2) ?_ ?_
    · exact fun i _=>mem_univ _
    intro i hi j hj hh; exact Prod.ext (((mem_filter.mp (show i∈s from hi)).2).trans ((mem_filter.mp (show j∈s from hj)).2).symm) hh
lemma bchip_A : ContDiffAt ℝ ω (bchip G f) 0:=by
    let p:=Army.powL (aleft G f).contDiff.contDiffAt (G:=G) (x:=0); have hp:= Army.powL (aright G f).contDiff.contDiffAt (G:=G) (x:=0)
    exact (hp.mul p|>.logL (by rw[map_zero,map_zero];simp))
variable {G f}
lemma bust (i:Edge (Site f))(u:Acr G f): edgeColor (bchip G f u) i=spout (edgeColor (aleft G f u) i) (edgeColor (aright G f u) i):=by
    unfold bchip; rw[show edgeColor (content _) _=_ from content_at (splitp G f u) i.1 i.2, splitp,Pi.mul_apply,input_color,input_color]; rfl
lemma spike_m (G:Gauge)(n:ℕ):∃ A, 0 ≤ A ∧ ∀ f:Side,∀ (j:Edge (Site f)), ∀ a:Acr G f→G.Color × G.Color, a=(fun z=>(edgeColor (aleft G f z) j,edgeColor (aright G f z) j)) → Allows n a 0 A:=by
    let L: (G.ColorIndex→ℝ)→L[ℝ] G.Color:= (WithLp.linearEquiv 2 ℝ _).symm.toContinuousLinearMap
    refine ⟨‖L‖*1,by positivity,fun f j _ ha=>?_⟩; rw[ha]
    refine Allows.pair (Allows.linear L (f:=fun x:Acr G f=> fun i=>edgeColor (aleft G f x) j i) ?_ le_rfl) (Allows.linear L (f:=fun x:Acr G f=>fun i=>edgeColor (aright G f x) j i) ?_ le_rfl)
    · apply allows_pi zero_le_one; intro i; let V:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:pairA G f=> ℝ) (Sum.inl (j.1,coord j.2,i))
      exact allows_linear (L:=V) (V.opNorm_le_bound zero_le_one (fun x=> by rw [one_mul]; exact norm_le_pi_norm x _)) (by rw[map_zero,norm_zero];norm_num)
    apply allows_pi zero_le_one; intro i; let V:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:pairA G f=> ℝ) (Sum.inr (j.1,coord j.2,i)); exact allows_linear (L:=V) (V.opNorm_le_bound zero_le_one (fun x=> by rw [one_mul]; exact norm_le_pi_norm x _)) (by rw[map_zero,norm_zero];norm_num)
lemma spoke0 (G:Gauge) (f:Side)(e:Edge (Site f)){a b:Acr G f} (h:∀ i, separation e.1 (af G f i) ≤ 0→ a i=b i):
    edgeColor (aleft G f a) e=edgeColor (aleft G f b) e ∧ edgeColor (aright G f a) e=edgeColor (aright G f b) e:=by
    constructor
    · ext i; exact h (.inl (e.1,coord e.2,i)) (show separation e.1 e.1 ≤0 by simp)
    ext i; exact h (.inr (e.1,coord e.2,i)) (show separation e.1 e.1≤0 by simp)
lemma speak (G:Gauge)(n:ℕ): ∃ A,0≤A∧∀ f:Side,Drive (af G f) Prod.fst (bchip G f) n A:=by
    let L:= uncurry (spout (G:=G)); obtain ⟨S,hS,h⟩:= exists_allows (s:={(0:G.Color×G.Color)}) (f:=L) (isCompact_singleton) (fun x hx=> hx.symm ▸ spout_cont _) n
    obtain ⟨T,hT,hx⟩:= spike_m G n
    let N(i:G.ColorIndex): G.Color →L[ℝ] ℝ := EuclideanSpace.proj i
    let C:= composeCost n S T
    have hp:0 ≤ C:=by unfold C composeCost; positivity
    refine ⟨(∑ i: G.ColorIndex, ‖N i‖) *C,by positivity,fun f=>?_⟩
    have hv(i:Lines G f 1): ContDiffAt ℝ ω (fun x=> bchip G f x i) 0:= (contDiffAt_apply ℝ ℝ i _).comp _ (bchip_A G f)
    have he(i:Edge (Site f))(k:G.ColorIndex): (fun z=> bchip G f z (i.1,coord i.2,k))=fun z=> N k (L (edgeColor (aleft G f z) i,edgeColor (aright G f z) i)):=by ext1 z; exact congr_arg (N k) (bust i z)
    refine ⟨bchip_A G f, ?_,?_⟩
    · rintro ⟨i,a,k⟩ j hj q
      obtain ⟨a,rfl⟩:= axisEquiv.surjective a
      rw [show ((fun z=> bchip G f z (i,axisEquiv a,k)))=_ from he (i,a) k]; apply (entry_bound ..).trans
      let X(v:Acr G f):=(edgeColor (aleft G f v) (i,a),edgeColor (aright G f v) (i,a))
      have hz : X 0=0:=Prod.ext (by simp[X]) (by simp[X])
      apply ((Allows.linear (f:=fun z=> L (X z)) (N k) (Allows.comp (g:=L) (hz.symm ▸ h _ (Set.mem_singleton _)) (hx _ _ X rfl)) (Finset.single_le_sum (fun i _=>norm_nonneg (N i)) (mem_univ k))).norm_le j hj).trans_eq (by rfl)
    rintro ⟨i,a,k⟩ j hj q h p; obtain ⟨a,rfl⟩:= axisEquiv.surjective a
    by_contra hp; apply h; let N:= fun z=>bchip G f z (i,axisEquiv a,k)
    have hr: Requests Set.univ N (af G f) i 0:=by
        rw [show N=_ from he (i,a) k]; intro z _ b _ h; dsimp only; obtain ⟨hz,hV⟩:= spoke0 _ _ (i,a) h; rw [hz,hV]
    refine hr.zero univ_mem ((hv _).of_le le_top) q p (fun he=>hp ?_)
    apply Eq.symm; change i=af G f (q p); change pdist _≤0 at he; have h:=Nat.eq_zero_of_le_zero he; by_contra hh; exact Nat.not_lt.mpr he (pdist_pos (sub_ne_zero.mpr hh))
end YM.Trace.Det
