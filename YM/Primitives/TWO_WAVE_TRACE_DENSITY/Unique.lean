import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Period
import YM.Progress.JOINT_CALENDAR.Branches
import YM.Push.FREE_RESOLVENT.Torus
import YM.Push.PRICE_COMPILER.Post

/-!
# The *infinite* symbols really fixed by the period family

In particular the inverse in `litBill` really is the symbol inverse there,
not just some analytic stencil agreeing on a mesh while secretly using
period-dependent covers. All LARGE periods suffice. Use also on retained Beds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.TwoWave
open Lattice Laurent RG Bloch FreeResolvent Filter Function Topology Matrix
open Work.F08
open scoped Classical BigOperators Topology
variable {n:Side}{k:ℕ}{α β ι τ:Type}

-- arbitrary sequence of growing comparison tori
lemma fan_fade {F:Fan α β k} (n:ℕ→Side)(h:Tendsto (fun q:ℕ=> (n q).val) atTop atTop) {η C:ℝ}(he:Cap F η C) (hη:0≤η)(a b w):
    Tendsto (fun q:ℕ=> pieces F (n q) (0,a) (floated 0 b w)) atTop (𝓝 (F a b w)) := by
  let R:= fun q (z:Shift (Arm k))=> if floated (n:=n q) 0 b w=floated (n:=n q) 0 b z then F a b z else 0
  let u:= fun z:Shift (Arm k)=> if w=z then F a b z else 0
  have hw (z) : Tendsto (fun q => R q z) atTop (𝓝 (u z)):= by
    by_cases hv:w=z
    · simp [R,u,hv]
    obtain ⟨⟨v,i⟩,hi⟩ : ∃ i,w i ≠ z i:= Function.ne_iff.mp hv
    let M:=max (size (point w v)) (size (point z v))
    refine (tendsto_const_nhds (x:=u z)).congr' ?_
    filter_upwards [h.eventually (eventually_gt_atTop (2*M))] with q hq
    unfold u R; rw [if_neg hv,if_neg]; intro H; apply hi
    change point w v i=point z v i
    have hh := add_left_cancel (a:=(0:Site (n q))) (congr_arg Prod.fst (congr_fun H v))
    rw [← size_centers (n q) (point w v) (le_max_left ..) hq,hh,size_centers _ _ (le_max_right ..) hq]
  have hs:= (he a b|>.unweighted hη).2.1
  have hv: Tendsto (fun q=>∑' z,R q z) atTop (𝓝 (∑' z,u z)):= tendsto_tsum_of_dominated_convergence hs hw (Eventually.of_forall fun q z=>by unfold R; split; exact le_rfl; rw [norm_zero]; exact norm_nonneg _)
  have ht:(∑' z,u z)=F a b w:=by rw [tsum_eq_single w]; exact if_pos rfl; intro z H; exact if_neg (Ne.symm H)
  rw [ht] at hv; exact hv

theorem fan_frozen {F G:Fan α β k}{η a s b:ℝ}(hF:Cap F η a)(h:0≤η)(hG:Cap G s b)(he:0≤s)
    (hp:∀ᶠ d:ℕ in atTop,∀ n:Side,d≤n.val→pieces F n=pieces G n) : F=G:=by
  obtain ⟨d,hp⟩:=hp.exists
  let n (i:ℕ):Side:=⟨i+d+1,by omega⟩
  have hh:Tendsto (fun q:ℕ=> (n q).val) atTop atTop:=tendsto_atTop_atTop.mpr (fun i=>⟨i,fun q hq=>by change i≤q+d+1; omega⟩)
  funext a b z; apply tendsto_nhds_unique (fan_fade n hh hF h a b z)
  refine (fan_fade n hh hG he a b z).congr (fun i=> ?_); rw [hp (n i) (by change d ≤ i+d+1; omega)]

-- equivalence of Cover indexing at arity one

def pageLine : Cover ≃ Shift (Arm 1) where
  toFun z a:=z a.2
  invFun z:= point z 0
  left_inv _:=rfl
  right_inv w:=by ext1 ⟨l,i⟩; fin_cases l; rfl



def row (F:Fan α β 1):Row α β:=fun i j z=>F i ![j] (pageLine z)


variable [Fintype β]
lemma head_periods (F:Fan α β 1)(n:Side) : (row F).acts n = headMatrix (pieces F n):=by
  ext i j; rw [headMatrix_at]; simp only [Row.acts,of_apply,pieces]
  rw [← pageLine.tsum_eq (fun z=> if ![j]=floated i.1 (Prod.snd ∘ (![j] : Fin 1→Leaf n β)) z then F i.2 _ z else 0)]
  apply tsum_congr; intro z
  have he : Prod.snd ∘ (![j]:Fin 1→Leaf n β)=![j.2]:=by ext1 l; fin_cases l; rfl
  rw [he]
  unfold row; split <;> rename_i h
  · rw [if_pos]; ext1 l; fin_cases l; exact Prod.ext h rfl
  rw [if_neg]; intro H
  exact h (congr_arg Prod.fst (congr_fun H 0))


-- allow all LARGE


-- Row product even on complex collar (analytic inverse release)



variable [DecidableEq α][Fintype α]

end YM.Primitives.TwoWave
