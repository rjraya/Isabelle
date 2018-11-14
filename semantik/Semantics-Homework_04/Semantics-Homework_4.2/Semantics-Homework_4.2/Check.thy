theory Check
  imports Submission
begin

theorem path_distinct:
  assumes "is_path E u p v"
  shows "\<exists>p'. distinct p' \<and> is_path E u p' v"
  using assms by (rule Submission.path_distinct)

end