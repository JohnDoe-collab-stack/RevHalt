# ==============================================================================
# Main Script - R Random Project
# ==============================================================================

# Load utility functions
source("utils.R")

# ------------------------------------------------------------------------------
# Configuration
# ------------------------------------------------------------------------------

set.seed(42)  # For reproducibility

# ------------------------------------------------------------------------------
# Main Execution
# ------------------------------------------------------------------------------

main <- function() {
  cat("Welcome to R Random Project!\n")
  cat("============================\n\n")
  
  # Example: Generate some random data
  n <- 100
  data <- generate_random_data(n)
  
  cat(sprintf("Generated %d random observations\n", n))
  cat(sprintf("Mean: %.4f\n", mean(data$value)))
  cat(sprintf("SD:   %.4f\n", sd(data$value)))
  
  # Return data for further analysis
  return(data)
}

# Run main function
if (interactive()) {
  result <- main()
}
