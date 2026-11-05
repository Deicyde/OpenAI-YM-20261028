import YM.RG08.Cell.Grid

/-!
# Native link coefficient difference -> packed color precision matrix
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Cell
open Stationary Function Matrix Lattice Exterior Precision RG Tree Wilson Laurent Bloch Finset RG08.Rows RG08.Flat Pert.Bulk RG08.Packets RG08.Line
open scoped Matrix BigOperators Topology Classical ENNReal
variable {α β:Type} {c f:Side}{p σ:ℝ}
variable {K : Kernel α β}
-- Translation implies every-root absolute sums (per type).
lemma col_of_row (h:city 1 K)(hp:RowCost σ 1 K p): ColCost σ 1 K p:=by
  intro i v
  let e:Cover≃Cover:=(Equiv.neg _).trans (Equiv.addRight v.1)
  have he (x:Cover):e x=v.1-x:=by change -x+v.1=_; abel
  rw [← e.tsum_eq]
  have hh x : K (e x,i) v=K (0,i) (x,v.2):=by
    have H:=h (0,i) (x,v.2) (v.1-x)
    rw [show (1:Side).val=1 from rfl,one_smul] at H
    simpa only [pass,zero_add,add_sub_cancel,he] using H
  simp_rw [hh,he,delta_one]
  have hw v x : Pert.Bulk.sep (v-x) v=Pert.Bulk.sep 0 x:=by unfold Pert.Bulk.sep; exact congr_arg Pert.Bulk.length (by abel)
  simp_rw [hw]; simpa only [delta_one] using hp (0,i) v.2

-- pigment generalized

def color (G:Gauge)(K : Kernel α β): Kernel (α × G.ColorIndex) (β × G.ColorIndex) := fun x y=> if x.2.2=y.2.2 then K (x.1,x.2.1) (y.1,y.2.1) else 0

theorem color_tagged (G:Gauge){i j :ℕ}{K : Kernel (TypeFace i) (TypeFace j)}{M:∀ n:Side,Matrix (Body i n) (Body j n) ℝ}(h:Tagged σ p K M) : Tagged σ p (color G K) (fun n=> patron G (M n)) := by
  refine ⟨⟨h.pos,fun x y u=>?_, fun x j=>?_,fun j x=>?_⟩,fun n x y=>?_⟩
  · unfold color; dsimp [Packets.pass]; split
    · exact h.city (x.1,x.2.1) (y.1,y.2.1) u
    rfl
  · unfold color; dsimp only
    by_cases he:x.2.2=j.2
    · simp_rw [if_pos he]; exact h.row (x.1,x.2.1) _
    simp [he,bill]
  · unfold color; dsimp only
    by_cases he:j.2=x.2.2
    · simp_rw [if_pos he]; exact h.col _ (x.1,x.2.1)
    simp [he,bill]
  rw [display]; obtain ⟨x,a,b⟩:=x; obtain ⟨y,u,v⟩:=y
  change (∑' z:Cover,_)=patron G (M n) (wrap n x,a,b) (y,u,v)
  rw [patron_cell G _ ((wrap n x,a):Body i n) ((y,u):Body j n) b v]
  unfold color; dsimp only
  by_cases he:b=v
  · simp only [if_pos he]; exact h.seen n (x,a) (y,u)
  simp [he]

lemma output_city (b:Bed): city 1 (output b):=by
  have h : city 1 (plain (cobound 1)) := pass_one _
  have hx : city 1 (second (saddle (b.metric))):=pass_one _
  have hg : city 1 (swap (plain (cobound 1))) := by
    intro x y z; simpa only [swap,show (1:Side).val=1 from rfl,one_smul] using h y x z
  unfold output writ
  simpa only [one_mul] using pass_bind hg (pass_bind hx h)

def changeK (b f:Bed): Kernel (TypeFace 1) (TypeFace 1) := fun x y=> output b x y-output f x y
lemma changeRow {b f:Bed}{τ r:ℝ}(h:RowCost σ 1 (changeK b f) p)(hp:0≤p)
    (hb:b.metric.strip τ r)(hf:f.metric.strip τ r) (hτ:0≤τ) (hr:0≤r): Tagged σ p (changeK b f) (fun n=> quadratic b n-quadratic f n):= by
  have he : city 1 (changeK b f):= fun x y v=> congr_arg₂ (fun a b:ℝ=>a-b) (output_city b x y v) (output_city f x y v)
  obtain ⟨ha,hA⟩:= Flat.output_cost (σ:=min 1 τ) (Y:=b) (p:=r) (fun i k=> (hb i k).mono (min_le_right ..) le_rfl) hr (le_min (by norm_num) hτ) (min_le_left ..)
  obtain ⟨hc,hC⟩:= Flat.output_cost (σ:=min 1 τ) (Y:=f) (p:=r) (fun i k=> (hf i k).mono (min_le_right ..) le_rfl) hr (le_min (by norm_num) hτ) (min_le_left ..)
  refine ⟨⟨hp,he,h,col_of_row he h⟩,fun n x y=>?_⟩
  exact (Flat.display_sub _ _ (cost_any ha (le_min (by norm_num) hτ) _) (cost_any hc (le_min (by norm_num) hτ) _)).trans (congr_arg₂ (fun a b:ℝ=>a-b) (hA n x y) (hC n x y))
end YM.RG08.Cell
